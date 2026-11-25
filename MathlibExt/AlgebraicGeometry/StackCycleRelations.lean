/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackCycleGeometry
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Naive stack rational equivalence and normalized cycle operations

The atlas pullback of a generator is the integral fundamental cycle of its
actual closed scheme fibre. Principal cycles are characterized on every
integral smooth atlas by native function-field order. Closed pushforward
is the map of free groups on the actual image cut, fixed on all scheme points.
These give Kresch's naive quotient, which is kept separate from his final
vector-bundle/projective colimit construction.

Reference: Kresch arXiv:math/9810166v1, Definition2.1.4(i)--(ii).
Ordinary closed-scheme Noetherianness is a proof-only source dependency,
not a new cycle carrier or a newly requested scheme theorem.
-/

@[expose] public noncomputable section
namespace AlgebraicGeometry.StackCycleRelations

open CategoryTheory CategoryTheory.Limits Opposite
open GeneralStackGeometry StackCycleGeometry

variable {S : Scheme.{0}}

structure AtlasGeometry (X : Stack S) where
  noetherian : ∀ (d : ℤ) (Z : IntegralClosedSubstack X d) (a : CycleAtlas X),
    IsNoetherian (Z.val.fibre a.atlas.U a.atlas.point).left

def atlasGenerator {X : Stack S} (G : AtlasGeometry X) (a : CycleAtlas X)
    {d : ℤ} (Z : IntegralClosedSubstack X d) : AlgebraicCycle a.atlas.U.left ℤ := by
  letI := G.noetherian d Z a
  exact AlgebraicCycle.map (Z.val.fibre a.atlas.U a.atlas.point).hom
    Order.height Order.height
    (integralFundamentalCycle (Z.val.fibre a.atlas.U a.atlas.point).left)

def atlasPull {X : Stack S} (G : AtlasGeometry X) (a : CycleAtlas X) (d : ℤ) :
    CycleGroup X d →+ AlgebraicCycle a.atlas.U.left ℤ :=
  FreeAbelianGroup.lift (atlasGenerator G a)

/-- The image cut is fixed on the actual fibre objects and isomorphisms. -/
structure ClosedPushData {X : Stack S} (C : ClosedSubstack X) where
  image : ∀ (d : ℤ), IntegralClosedSubstack C.source d → IntegralClosedSubstack X d
  normalized : ∀ (d : ℤ) (Z : IntegralClosedSubstack C.source d)
      (T : Over S) (x : X.Fibre T),
    (image d Z).val.predicate T x ↔ ∃ y : C.source.Fibre T,
      Nonempty ((StackCycleGeometry.component C.inclusion T).obj y ≅ x) ∧
      Z.val.predicate T y

def closedPush {X : Stack S} {C : ClosedSubstack X} (P : ClosedPushData C) (d : ℤ) :
    CycleGroup C.source d →+ CycleGroup X d := FreeAbelianGroup.map (P.image d)

/-- No principal-cycle oracle: every coefficient is the native local order
after the actual smooth-atlas cycle pullback. -/
def IsPrincipalCycle {X : Stack S} (G : AtlasGeometry X) (d : ℤ)
    (f : RationalUnitFamily X) (c : CycleGroup X d) : Prop :=
  ∀ (a : IntegralAtlas X) (x : a.atlas.U.left),
    atlasPull G a.toCycleAtlas d c x = a.atlas.U.left.ord (f.value a) x

structure PrincipalCycleData (X : Stack S) where
  geometry : AtlasGeometry X
  divisor : ∀ (d : ℤ), HasIntegralDimension X (d + 1) →
    RationalUnitFamily X → CycleGroup X d
  normalized : ∀ (d : ℤ) (h : HasIntegralDimension X (d + 1))
      (f : RationalUnitFamily X), IsPrincipalCycle geometry d f (divisor d h f)

/-- The actual point relation of the native étale presentation. -/
def SpacePointRelated {T : Scheme.{0}} (A : AlgebraicSpaceOver T)
    (x y : A.presentation.U) : Prop :=
  ∃ r : A.presentation.R, A.presentation.source r = x ∧ A.presentation.target r = y

/-- Relative quasi-compactness through actual finite affine atlas image
covers. The orbit condition is the literal étale relation, so an arbitrary
infinite atlas is not mistaken for a quasi-compact structural morphism. -/
def SpaceChartQuasiCompact {T : Scheme.{0}} {A : AlgebraicSpaceOver T} (c : A.Chart) : Prop :=
  ∀ V : T.affineOpens, ∃ s : Finset A.presentation.U.affineOpens,
    (∀ W ∈ s, W.1 ≤ c.map ⁻¹ᵁ V.1) ∧
    ∀ x : A.presentation.U, c.map x ∈ V.1 →
      ∃ (W : A.presentation.U.affineOpens) (_ : W ∈ s) (y : A.presentation.U),
        y ∈ W.1 ∧ Relation.EqvGen (SpacePointRelated A) x y

/-- The older algebraic-stack diagonal convention used by Kresch through
[A,L-MB]: separated and quasi-compact representable diagonal. Closedness
is checked on the actual relation map R→U×_T U, rather than assumed from
finite type of a chosen stack atlas. -/
def HasKreschDiagonal {S : Scheme.{0}} (X : Stack S) : Prop :=
  ∀ (T : Over S) (x y : X.Fibre T), ∃ A : AlgebraicSpaceOver T.left,
    Nonempty (relativeSpacePresheaf T A ≅
      X.toPseudofunctor.presheafHom x y ⋙ uliftFunctor.{1, 0}) ∧
    ∃ (c : A.Chart)
      (h : A.presentation.source ≫ c.map = A.presentation.target ≫ c.map),
      SpaceChartQuasiCompact c ∧
      IsClosedImmersion (pullback.lift A.presentation.source A.presentation.target h)

/-- Finite type with the explicit source-qualified diagonal convention.
Generic native Artin stacks with custom scope remain separate. -/
def FiniteTypeArtin (k : Type) [Field k] (X : Stack (Spec (.of k))) : Prop :=
  X.HasRepresentableDiagonal ∧ HasKreschDiagonal X ∧ ∃ a : X.SmoothAtlas,
    LocallyOfFiniteType a.U.hom ∧ QuasiCompact a.U.hom

/-- Cycle operations on a class `scope` of stacks over $S$ that is closed under passing to closed
substacks (`closedScope`). For every stack $X$ in the class, principal cycles (`principal`): when
$X$ has integral dimension $d + 1$ (`HasIntegralDimension`), a $d$-cycle $\mathrm{div}(f)$ for
every rational function $f$ on $X$ (a compatible family of units of the function fields of its
integral atlases), whose pullback to every integral smooth atlas is the divisor of orders of $f$
there, these pullbacks being defined through the Noetherian atlas fibres of integral closed
substacks. For every closed substack $C$ of $X$ (`closedImage`): the image in $X$ of every
integral closed substack $Z$ of $C$ of dimension $d$, an integral closed substack of dimension $d$
whose objects are those isomorphic to images of objects of $Z$. -/
structure CycleConstructionData (S : Scheme.{0}) (scope : Stack S → Prop) where
  closedScope : ∀ (X : Stack S), scope X → ∀ C : ClosedSubstack X, scope C.source
  principal : ∀ (X : Stack S), scope X → PrincipalCycleData X
  closedImage : ∀ (X : Stack S), scope X → ∀ C : ClosedSubstack X, ClosedPushData C

variable {scope : Stack S → Prop}

def IsRationalRelation (D : CycleConstructionData S scope) (X : Stack S) (hX : scope X)
    (d : ℤ) (c : CycleGroup X d) : Prop :=
  ∃ (C : IntegralClosedSubstack X (d + 1)) (f : RationalUnitFamily C.val.source),
    c = closedPush (D.closedImage X hX C.val) d
      ((D.principal C.val.source (D.closedScope X hX C.val)).divisor d C.property f)

def rationalRelations (D : CycleConstructionData S scope) (X : Stack S) (hX : scope X) (d : ℤ) :
    AddSubgroup (CycleGroup X d) := AddSubgroup.closure {c | IsRationalRelation D X hX d c}

abbrev NaiveChowGroup (D : CycleConstructionData S scope) (X : Stack S) (hX : scope X)
    (d : ℤ) := CycleGroup X d ⧸ rationalRelations D X hX d

def naiveCycleClass (D : CycleConstructionData S scope) (X : Stack S) (hX : scope X) (d : ℤ) :
    CycleGroup X d →+ NaiveChowGroup D X hX d := QuotientAddGroup.mk' _

/-- Flat cycle pullback is fixed on free generators by their actual scheme
fibres at every atlas point. Quotient descent is a separate proof field. -/
structure FlatPullData (D : CycleConstructionData S scope) {X Y : Stack S}
    (hX : scope X) (hY : scope Y) (f : StackHom X Y) (shift : ℤ) where
  cycle : ∀ d : ℤ, CycleGroup Y d →+ CycleGroup X (d + shift)
  fibreNoetherian : ∀ (d : ℤ) (Z : IntegralClosedSubstack Y d) (a : CycleAtlas X),
    IsNoetherian (Z.val.fibre a.atlas.U
      ((StackCycleGeometry.component f a.atlas.U).obj a.atlas.point)).left
  normalized : ∀ (d : ℤ) (Z : IntegralClosedSubstack Y d) (a : CycleAtlas X),
    letI := fibreNoetherian d Z a
    atlasPull (D.principal X hX).geometry a (d + shift) (cycle d (cycleClass Z)) =
      AlgebraicCycle.map (Z.val.fibre a.atlas.U
        ((StackCycleGeometry.component f a.atlas.U).obj a.atlas.point)).hom
        Order.height Order.height
        (integralFundamentalCycle (Z.val.fibre a.atlas.U
          ((StackCycleGeometry.component f a.atlas.U).obj a.atlas.point)).left)
  descends : ∀ (d : ℤ) (c : CycleGroup Y d),
    c ∈ rationalRelations D Y hY d → cycle d c ∈ rationalRelations D X hX (d + shift)

def FlatPullData.onChow {D : CycleConstructionData S scope} {X Y : Stack S}
    {hX : scope X} {hY : scope Y} {f : StackHom X Y} {shift : ℤ}
    (F : FlatPullData D hX hY f shift) (d : ℤ) :
    NaiveChowGroup D Y hY d →+ NaiveChowGroup D X hX (d + shift) :=
  QuotientAddGroup.map _ _ (F.cycle d) (F.descends d)

end AlgebraicGeometry.StackCycleRelations
