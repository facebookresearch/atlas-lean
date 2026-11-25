/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The cycle vocabulary follows Andrew Kresch, Cycle groups for Artin stacks,
arXiv:math/9810166v1, Definitions 2.1.3--2.1.11 and Theorem 2.1.12.
Scheme cycle multiplicities adapt the completed Meta GeometricChow module
and AxiomMath/Stacks, c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Chow/Vocabulary.lean and
CycleAssociatedClosed/Basic.lean (Apache License 2.0).
Modification: use integral coefficients, signed stack dimensions and actual
closed subfunctors of the native relative fppf stack. No scheme Chow theorem
or abstract replacement carrier is asserted to be missing.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralStackGeometry
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.OrderOfVanishing.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.RingTheory.Length
public import Mathlib.Topology.KrullDimension

/-!
# Integral stack cycles with geometric presentations

A closed substack is a full cut of the actual fibre groupoids. Its pullback
along every scheme-valued point is a genuine closed subscheme, characterized
on all scheme maps, including nonreduced tests. The chosen stack realization
is normalized by its fully faithful inclusion and exact essential image.

The integral cycle group is free on these closed cuts with an actual integral
smooth atlas of signed dimension `dim U - relativeRank`. Atlas dimensions and
function fields use native schemes and generic-point stalks. Rational units
are compatible units in those fields under actual dominant chart maps.

This is the cycle vocabulary for Kresch's construction, not the naive quotient
misidentified with integral Artin-stack Chow. Vector-bundle and projective
presentation systems are supplied in the companion Chow module. Their
construction/functoriality proofs are separate Wanted endpoints.
-/

@[expose] public noncomputable section
namespace AlgebraicGeometry.StackCycleGeometry

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open GeneralStackGeometry

abbrev Stack (S : Scheme.{0}) := RelativeStack S

abbrev StackHom {S : Scheme.{0}} (X Y : Stack S) :=
  Pseudofunctor.StrongTrans X.toPseudofunctor Y.toPseudofunctor

abbrev pull {S : Scheme.{0}} (X : Stack S) {T V : Over S} (a : V ⟶ T) :
    X.Fibre T ⥤ X.Fibre V :=
  (X.toPseudofunctor.map a.op.toLoc).toFunctor

abbrev component {S : Scheme.{0}} {X Y : Stack S} (f : StackHom X Y)
    (T : Over S) : X.Fibre T ⥤ Y.Fibre T :=
  (f.app (.mk (op T))).toFunctor

variable {S : Scheme.{0}}

/-- A closed full cut, tested on actual groupoid objects and scheme maps.
All fields except the predicate are propositions, so equivalent chosen
presentations do not give distinct cycle generators. -/
structure ClosedSubstack (X : Stack S) where
  predicate : ∀ T : Over S, X.Fibre T → Prop
  pull_mem : ∀ {T V : Over S} (a : V ⟶ T) (x : X.Fibre T),
    predicate T x → predicate V ((pull X a).obj x)
  iso_mem : ∀ (T : Over S) (x y : X.Fibre T), Nonempty (x ≅ y) →
    (predicate T x ↔ predicate T y)
  represented : ∀ (T : Over S) (x : X.Fibre T), ∃ Z : Over T.left,
    IsClosedImmersion Z.hom ∧
    ∀ (V : Over S) (a : V ⟶ T), predicate V ((pull X a).obj x) ↔
      ∃ b : V.left ⟶ Z.left, b ≫ Z.hom = a.left
  realization : ∃ (Y : Stack S) (f : StackHom Y X),
    Nonempty (∀ T : Over S, (component f T).FullyFaithful) ∧
    ∀ (T : Over S) (x : X.Fibre T), predicate T x ↔
      ∃ y : Y.Fibre T, Nonempty ((component f T).obj y ≅ x)

def ClosedSubstack.source {X : Stack S} (Z : ClosedSubstack X) : Stack S :=
  Classical.choose Z.realization

def ClosedSubstack.inclusion {X : Stack S} (Z : ClosedSubstack X) :
    StackHom Z.source X := Classical.choose (Classical.choose_spec Z.realization)

def ClosedSubstack.inclusion_fullyFaithful {X : Stack S}
    (Z : ClosedSubstack X) (T : Over S) :
    (component Z.inclusion T).FullyFaithful :=
  Classical.choice (Classical.choose_spec (Classical.choose_spec Z.realization)).1 T

theorem ClosedSubstack.inclusion_image {X : Stack S} (Z : ClosedSubstack X)
    (T : Over S) (x : X.Fibre T) : Z.predicate T x ↔
      ∃ y : Z.source.Fibre T, Nonempty ((component Z.inclusion T).obj y ≅ x) :=
  (Classical.choose_spec (Classical.choose_spec Z.realization)).2 T x

def ClosedSubstack.fibre {X : Stack S} (Z : ClosedSubstack X)
    (T : Over S) (x : X.Fibre T) : Over T.left :=
  Classical.choose (Z.represented T x)

instance ClosedSubstack.fibre_closed {X : Stack S} (Z : ClosedSubstack X)
    (T : Over S) (x : X.Fibre T) : IsClosedImmersion (Z.fibre T x).hom :=
  (Classical.choose_spec (Z.represented T x)).1

theorem ClosedSubstack.fibre_normalized {X : Stack S} (Z : ClosedSubstack X)
    (T : Over S) (x : X.Fibre T) (V : Over S) (a : V ⟶ T) :
    Z.predicate V ((pull X a).obj x) ↔
      ∃ b : V.left ⟶ (Z.fibre T x).left, b ≫ (Z.fibre T x).hom = a.left :=
  (Classical.choose_spec (Z.represented T x)).2 V a

/-- The actual smooth atlas and its constant relative dimension. -/
structure CycleAtlas (X : Stack S) where
  atlas : X.SmoothAtlas
  [noetherian : IsNoetherian atlas.U.left]
  [finiteType : LocallyOfFiniteType atlas.U.hom]
  relativeRank : ℕ
  rank_normalized : ∀ (T : Over S) (x : X.Fibre T),
    ∃ c : (atlas.baseChange T x).Chart,
      SmoothOfRelativeDimension relativeRank c.map

attribute [instance] CycleAtlas.noetherian CycleAtlas.finiteType

/-- Integral charts use actual generic-point function fields. -/
structure IntegralAtlas (X : Stack S) extends CycleAtlas X where
  [integral : IsIntegral atlas.U.left]
  schemeDimension : ℕ
  schemeDimension_eq : topologicalKrullDim atlas.U.left = (schemeDimension : ℕ)

attribute [instance] IntegralAtlas.integral

def IntegralAtlas.signedDimension {X : Stack S} (a : IntegralAtlas X) : ℤ :=
  (a.schemeDimension : ℤ) - a.relativeRank

def HasIntegralDimension (X : Stack S) (d : ℤ) : Prop :=
  ∃ a : IntegralAtlas X, a.signedDimension = d

/-- Integral closed stack components with their genuine signed grading. -/
abbrev IntegralClosedSubstack (X : Stack S) (d : ℤ) :=
  {Z : ClosedSubstack X // HasIntegralDimension Z.source d}

/-- Integral cycles are free on actual closed full cuts, not on atlas names. -/
abbrev CycleGroup (X : Stack S) (d : ℤ) :=
  FreeAbelianGroup (IntegralClosedSubstack X d)

def cycleClass {X : Stack S} {d : ℤ} (Z : IntegralClosedSubstack X d) :
    CycleGroup X d := FreeAbelianGroup.of Z

abbrev ChartField {X : Stack S} (a : IntegralAtlas X) := a.atlas.U.left.functionField

/-- A dominant scheme map over the same stack, with the actual comparison
of the two scheme-valued points retained. -/
structure ChartArrow {X : Stack S} (a b : IntegralAtlas X) where
  map : a.atlas.U ⟶ b.atlas.U
  overStack : a.atlas.point ≅ (pull X map).obj b.atlas.point
  generic : map.left (genericPoint a.atlas.U.left) = genericPoint b.atlas.U.left

def chartFieldPull {X : Stack S} {a b : IntegralAtlas X} (f : ChartArrow a b) :
    ChartField b ⟶ ChartField a :=
  eqToHom (congrArg (fun x => b.atlas.U.left.presheaf.stalk x) f.generic.symm) ≫
    f.map.left.stalkMap (genericPoint a.atlas.U.left)

/-- Rational units are compatible actual function-field units, rather than
an unrelated field assigned to the stack. -/
structure RationalUnitFamily (X : Stack S) where
  value : ∀ a : IntegralAtlas X, (ChartField a)ˣ
  naturality : ∀ (a b : IntegralAtlas X) (f : ChartArrow a b),
    (chartFieldPull f).hom (value b : ChartField b) = (value a : ChartField a)

/-- The principal cycle of a rational function $f$ on an integral Noetherian scheme $U$, as a
subtype: the algebraic cycles $c$ on $U$ with integer coefficients whose coefficient at every point
$x$ is `U.ord f x`, the order of vanishing of $f$ at $x$ when $x$ has codimension one and $0$ at
other points (and at every point when $f = 0$). -/
abbrev PrincipalSchemeCycle (U : Scheme.{0}) [IsIntegral U] [IsNoetherian U]
    (f : U.functionField) :=
  {c : AlgebraicCycle U ℤ // ∀ x : U, c x = U.ord f x}

/-- Integral fundamental cycles retain nilpotent generic multiplicities. -/
def integralFundamentalCycle (U : Scheme.{0}) [IsNoetherian U] :
    AlgebraicCycle U ℤ := by
  classical
  letI : Finite (irreducibleComponents U) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  letI := Fintype.ofFinite (irreducibleComponents U)
  exact ∑ Z : irreducibleComponents U,
    Function.locallyFinsuppWithin.single Z.2.1.genericPoint
      ((Module.length (U.presheaf.stalk Z.2.1.genericPoint)
        (U.presheaf.stalk Z.2.1.genericPoint)).toNat : ℤ)

end AlgebraicGeometry.StackCycleGeometry
