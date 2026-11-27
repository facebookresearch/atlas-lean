/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The scalar and Kähler-map formulas generalize the completed public Atlas core
MathlibExt/AlgebraicGeometry/ValuativeFanoGeometry.lean, at
534d1fe350d3adec419480b5ab33440a8b25be7f:
https://github.com/facebookresearch/atlas-lean/pull/2903
The source has the same Meta license notice. Modification notice: use any
perfect base field, actual normal codimension-one frames and real Weil-boundary data;
no smooth Fano or absolute-proper specialization is required here.
Native function-field/ord operations are Mathlib at
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing.DVR
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Topology.KrullDimension
public import MathlibExt.AlgebraicGeometry.RationalResolution
public import MathlibExt.AlgebraicGeometry.BirationalResolution
public import MathlibExt.AlgebraicGeometry.CurveVectorBundles
public import MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
public import MathlibExt.LinearAlgebra.ExteriorPowerSemilinear

/-!
# Actual normal log pairs and valuative discrepancy contracts

Boundary coefficients are finite real Weil cycles on native codimension-one
scheme points. Canonical coefficients use a nonzero rational top differential,
actual local/rational bases and Mathlib's order of vanishing. The base field
of canonical data, hence of log pairs, is perfect: then a normal variety is
smooth at its codimension-one points (their local rings are essentially smooth
over the field), so the top Kähler forms there are free of rank one and
canonical frames exist at every prime point. Over an
imperfect field the module of Kähler differentials of the function field can
have dimension larger than `n`, and the canonical divisor would have to come
from the dualizing module; that case is not modelled here. Cartier data
use actual affine opens and rational functions with unit transition maps;
their line bundles are pinned by genuine local sections and stalk generators.

These are minimal public data and map contracts. Canonical-frame, Cartier
gluing and birational comparison producers remain explicit dependencies;
no discrepancy, klt, contraction or termination conclusion is supplied as
arbitrary data. References: Hartshorne II.6; Kollár--Mori, §2.3, log pairs
and discrepancies. Native function fields, local orders and module stalks
are reused rather than replaced by numerical oracles.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LogPairs

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.TopologicalSpace Order
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurveVectorBundles
open MathlibExt.AlgebraicGeometry.CurvePositivity
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open MathlibExt.AlgebraicGeometry.BirationalResolution
open scoped BigOperators

universe u

structure NormalVariety (k : Type u) [Field k] (n : ℕ) where
  X : Over (Spec (.of k))
  [integral : IsIntegral X.left]
  [noetherian : IsNoetherian X.left]
  [separated : IsSeparated X.hom]
  [finiteType : LocallyOfFiniteType X.hom]
  [quasiCompact : QuasiCompact X.hom]
  normal : MathlibExt.AlgebraicGeometry.RationalResolution.IsNormalIntegral X.left
  dimension : topologicalKrullDim X.left = (n : ℕ)

attribute [instance] NormalVariety.integral NormalVariety.noetherian
  NormalVariety.separated NormalVariety.finiteType NormalVariety.quasiCompact

variable {k : Type u} [Field k] {n : ℕ}

/-- The codimension-one points of $V$: the points $x$ with $\operatorname{coheight}(x) = 1$ in the
specialization order ($x \le y$ when $x$ lies in the closure of $y$, so the generic point is the
top), in which the coheight of a point is its codimension. -/
abbrev PrimePoint (V : NormalVariety k n) := {x : V.X.left // coheight x = 1}
abbrev IntegerWeil (V : NormalVariety k n) := PrimePoint V →₀ ℤ
abbrev RealWeil (V : NormalVariety k n) := PrimePoint V →₀ ℝ
abbrev FunctionField (V : NormalVariety k n) := V.X.left.functionField
abbrev LocalRing (V : NormalVariety k n) (x : V.X.left) := V.X.left.presheaf.stalk x

def localScalar (V : NormalVariety k n) (x : V.X.left) : k →+* LocalRing V x :=
  (V.X.left.presheaf.germ ⊤ x (by trivial)).hom.comp (globalScalarMap V.X.hom)

def fractionScalar (V : NormalVariety k n) : k →+* FunctionField V :=
  letI : Nonempty (⊤ : V.X.left.Opens) := ⟨⟨genericPoint V.X.left, by trivial⟩⟩
  (V.X.left.germToFunctionField ⊤).hom.comp (globalScalarMap V.X.hom)

@[instance_reducible] def localAlgebra (V : NormalVariety k n) (x : V.X.left) :
    Algebra k (LocalRing V x) := (localScalar V x).toAlgebra

@[instance_reducible] def fractionAlgebra (V : NormalVariety k n) :
    Algebra k (FunctionField V) := (fractionScalar V).toAlgebra

def localToField (V : NormalVariety k n) (x : V.X.left) :
    letI : Algebra k (LocalRing V x) := localAlgebra V x
    letI : Algebra k (FunctionField V) := fractionAlgebra V
    LocalRing V x →ₐ[k] FunctionField V := by
  letI : Algebra k (LocalRing V x) := localAlgebra V x
  letI : Algebra k (FunctionField V) := fractionAlgebra V
  letI : Nonempty (⊤ : V.X.left.Opens) := ⟨⟨genericPoint V.X.left, by trivial⟩⟩
  refine { __ := algebraMap (LocalRing V x) (FunctionField V), commutes' := ?_ }
  intro a
  exact V.X.left.algebraMap_germ_eq_germToFunctionField (x := x) (U := ⊤)
    (by trivial) (globalScalarMap V.X.hom a)

/-- The native Kähler map, semilinear along the actual coefficient map. -/
def differentialMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) :
    KaehlerDifferential k R →ₛₗ[f.toRingHom] KaehlerDifferential k S := by
  letI : Algebra R S := f.toRingHom.toAlgebra
  letI : IsScalarTower k R S :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact (f.commutes a).symm)
  let g := KaehlerDifferential.map k k R S
  refine { toFun := g, map_add' := g.map_add, map_smul' := ?_ }
  intro a b
  rw [g.map_smul]
  rfl

abbrev LocalTopForms (V : NormalVariety k n) (x : V.X.left) :=
  letI : Algebra k (LocalRing V x) := localAlgebra V x
  ↥(⋀[LocalRing V x]^n (KaehlerDifferential k (LocalRing V x)))

abbrev RationalTopForms (V : NormalVariety k n) :=
  letI : Algebra k (FunctionField V) := fractionAlgebra V
  ↥(⋀[FunctionField V]^n (KaehlerDifferential k (FunctionField V)))

def localTopMap (V : NormalVariety k n) (x : V.X.left) :
    letI : Algebra k (LocalRing V x) := localAlgebra V x
    letI : Algebra k (FunctionField V) := fractionAlgebra V
    LocalTopForms V x →ₛₗ[(localToField V x).toRingHom] RationalTopForms V := by
  letI : Algebra k (LocalRing V x) := localAlgebra V x
  letI : Algebra k (FunctionField V) := fractionAlgebra V
  exact ExteriorAlgebra.powMapₛₗ n (localToField V x).toRingHom
    (differentialMap (localToField V x))

/-- An actual canonical frame and its normalized rational image. -/
structure CanonicalFrame (V : NormalVariety k n) (p : PrimePoint V) where
  localBasis : Module.Basis Unit (LocalRing V p.val) (LocalTopForms V p.val)
  rationalBasis : Module.Basis Unit (FunctionField V) (RationalTopForms V)
  normalized : rationalBasis () = localTopMap V p.val (localBasis ())

def canonicalCoefficient (V : NormalVariety k n) (eta : RationalTopForms V)
    (frames : ∀ p : PrimePoint V, CanonicalFrame V p) (p : PrimePoint V) : ℤ :=
  V.X.left.ord ((frames p).rationalBasis.repr eta ()) p.val

/-- Canonical data of a normal variety over a perfect field (field `perfect`): a
nonzero rational top form and frames of the top Kähler forms at every prime point.
Over a perfect field such frames always exist; over an imperfect field top forms
need not have rank one (see the module docstring), and this structure does not
model that case. -/
structure CanonicalData (V : NormalVariety k n) where
  [perfect : PerfectField k]
  form : RationalTopForms V
  nonzero : form ≠ 0
  frames : ∀ p : PrimePoint V, CanonicalFrame V p
  finite : (Function.support (canonicalCoefficient V form frames)).Finite

def canonicalDivisor {V : NormalVariety k n} (C : CanonicalData V) : IntegerWeil V :=
  Finsupp.ofSupportFinite (canonicalCoefficient V C.form C.frames) C.finite

abbrev ModuleStalk (X : Scheme.{u}) (L : X.Modules) (x : X) : Type u :=
  ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) L.presheaf x)

@[instance_reducible]
def moduleStalkModule (X : Scheme.{u}) (L : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (ModuleStalk X L x) := by
  let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := L.val
  change Module (X.presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)
  infer_instance

structure CartierAtlas (V : NormalVariety k n) where
  size : ℕ
  opens : Fin size → V.X.left.Opens
  affine : ∀ i, IsAffineOpen (opens i)
  nonempty : ∀ i, Nonempty (opens i)
  overlapNonempty : ∀ i j, Nonempty (opens i ⊓ opens j : V.X.left.Opens)
  covers : ∀ x : V.X.left, ∃ i, x ∈ opens i
  functions : Fin size → (FunctionField V)ˣ
  transitions : ∀ i j, Γ(V.X.left, opens i ⊓ opens j)ˣ
  transitionFunctions : ∀ i j,
    letI := overlapNonempty i j
    V.X.left.germToFunctionField (opens i ⊓ opens j) (transitions i j) =
      (functions i : FunctionField V) / functions j

def CartierAtlas.coefficient {V : NormalVariety k n} (D : CartierAtlas V)
    (p : PrimePoint V) : ℤ :=
  V.X.left.ord (D.functions (Classical.choose (D.covers p.val))) p.val

theorem CartierAtlas.coefficient_eq {V : NormalVariety k n} (D : CartierAtlas V)
    (p : PrimePoint V) (i : Fin D.size) (hi : p.val ∈ D.opens i) :
    D.coefficient p = V.X.left.ord (D.functions i) p.val := by
  let j := Classical.choose (D.covers p.val)
  have hj : p.val ∈ D.opens j := Classical.choose_spec (D.covers p.val)
  let := D.overlapNonempty i j
  have hu := V.X.left.ord_of_isUnit (Units.isUnit (D.transitions i j))
    (x := p.val) (show p.val ∈ D.opens i ⊓ D.opens j from ⟨hi, hj⟩)
  rw [D.transitionFunctions i j] at hu
  have hm := V.X.left.ord_mul (x := p.val)
    (div_ne_zero (Units.ne_zero (D.functions i)) (Units.ne_zero (D.functions j)))
    (Units.ne_zero (D.functions j))
  rw [div_mul_cancel₀ _ (Units.ne_zero (D.functions j)), hu, zero_add] at hm
  exact hm.symm

/-- Cartier data with its genuinely associated line and coherent frames. -/
structure CartierLine (V : NormalVariety k n) extends CartierAtlas V where
  line : LineBundle V.X.left
  sections : ∀ i, line.val.presheaf.obj (op (opens i))
  generators : ∀ i (x : V.X.left) (hx : x ∈ opens i),
    letI : Module (LocalRing V x) (ModuleStalk V.X.left line.val x) :=
      moduleStalkModule V.X.left line.val x
    Submodule.span (LocalRing V x)
      {TopCat.Presheaf.germ line.val.presheaf (opens i) x hx (sections i)} = ⊤
  transitionSections : ∀ i j (x : V.X.left) (hi : x ∈ opens i) (hj : x ∈ opens j),
    letI : Module (LocalRing V x) (ModuleStalk V.X.left line.val x) :=
      moduleStalkModule V.X.left line.val x
    TopCat.Presheaf.germ line.val.presheaf (opens i) x hi (sections i) =
      (((transitions i j).map (V.X.left.presheaf.germ (opens i ⊓ opens j) x ⟨hi, hj⟩).hom)⁻¹ :
        (LocalRing V x)ˣ) •
        TopCat.Presheaf.germ line.val.presheaf (opens j) x hj (sections j)
  finite : (Function.support toCartierAtlas.coefficient).Finite

def CartierLine.divisor {V : NormalVariety k n} (D : CartierLine V) : IntegerWeil V :=
  Finsupp.ofSupportFinite D.toCartierAtlas.coefficient D.finite

def realCast {V : NormalVariety k n} (D : IntegerWeil V) : RealWeil V :=
  D.mapRange (fun a : ℤ => (a : ℝ)) (by simp)

structure CartierCombination (V : NormalVariety k n) where
  size : ℕ
  components : Fin size → CartierLine V
  coefficients : Fin size → ℝ

def CartierCombination.divisor {V : NormalVariety k n} (D : CartierCombination V) : RealWeil V :=
  ∑ i, D.coefficients i • realCast (D.components i).divisor

/-- A log pair over a perfect field `k` (perfectness is recorded in its canonical
data): a normal variety, canonical data, an effective real boundary and an adjoint
Cartier combination representing `K + Δ`. -/
structure LogPair (k : Type u) [Field k] (n : ℕ) where
  variety : NormalVariety k n
  canonical : CanonicalData variety
  boundary : RealWeil variety
  effective : ∀ p, 0 ≤ boundary p
  adjoint : CartierCombination variety
  normalized : adjoint.divisor = realCast (canonicalDivisor canonical) + boundary

def LogPair.withAdjoint (P : LogPair k n) (D : CartierCombination P.variety)
    (h : D.divisor = realCast (canonicalDivisor P.canonical) + P.boundary) : LogPair k n :=
  { P with adjoint := D, normalized := h }

def genericMap {V W : NormalVariety k n} (f : W.X ⟶ V.X)
    (h : f.left (genericPoint W.X.left) = genericPoint V.X.left) :
    FunctionField V ⟶ FunctionField W :=
  eqToHom (congrArg (fun x => V.X.left.presheaf.stalk x) h.symm) ≫
    f.left.stalkMap (genericPoint W.X.left)

def rationalTopMap {V W : NormalVariety k n}
    (f : letI : Algebra k (FunctionField V) := fractionAlgebra V
      letI : Algebra k (FunctionField W) := fractionAlgebra W
      FunctionField V →ₐ[k] FunctionField W) :
    letI : Algebra k (FunctionField V) := fractionAlgebra V
    letI : Algebra k (FunctionField W) := fractionAlgebra W
    RationalTopForms V →ₛₗ[f.toRingHom] RationalTopForms W := by
  letI : Algebra k (FunctionField V) := fractionAlgebra V
  letI : Algebra k (FunctionField W) := fractionAlgebra W
  exact ExteriorAlgebra.powMapₛₗ n f.toRingHom (differentialMap f)

/-- Canonical comparison for a fixed actual birational morphism. The field
map is fixed by its genuine generic-point stalk map. -/
structure BirationalData (P : LogPair k n) (W : NormalVariety k n) (f : W.X ⟶ P.variety.X) where
  generic : f.left (genericPoint W.X.left) = genericPoint P.variety.X.left
  fieldIso :
    letI : Algebra k (FunctionField P.variety) := fractionAlgebra P.variety
    letI : Algebra k (FunctionField W) := fractionAlgebra W
    FunctionField P.variety ≃ₐ[k] FunctionField W
  fieldNormalized : fieldIso.toRingHom = (genericMap f generic).hom
  canonical : CanonicalData W
  formNormalized :
    letI : Algebra k (FunctionField P.variety) := fractionAlgebra P.variety
    letI : Algebra k (FunctionField W) := fractionAlgebra W
    canonical.form = rationalTopMap fieldIso.toAlgHom P.canonical.form

structure BirationalModel (P : LogPair k n) where
  variety : NormalVariety k n
  map : variety.X ⟶ P.variety.X
  [proper : IsProper map.left]
  birational : IsBirationalMorphism map.left
  data : BirationalData P variety map

attribute [instance] BirationalModel.proper

def BirationalModel.withAdjoint {P : LogPair k n} (M : BirationalModel P)
    (D : CartierCombination P.variety)
    (h : D.divisor = realCast (canonicalDivisor P.canonical) + P.boundary) :
    BirationalModel (P.withAdjoint D h) where
  variety := M.variety
  map := M.map
  proper := M.proper
  birational := M.birational
  data :=
    { generic := M.data.generic
      fieldIso := M.data.fieldIso
      fieldNormalized := M.data.fieldNormalized
      canonical := M.data.canonical
      formNormalized := M.data.formNormalized }

/-- The explicit shared producer contract ensures every genuine proper
normal birational model can be equipped with this normalized calculus. -/
class HasModelCalculus (P : LogPair k n) : Prop where
  data : ∀ (W : NormalVariety k n) (f : W.X ⟶ P.variety.X) [IsProper f.left],
    IsBirationalMorphism f.left → Nonempty (BirationalData P W f)

def pulledCartierCoefficient {P : LogPair k n} (M : BirationalModel P)
    (D : CartierLine P.variety) (p : PrimePoint M.variety) : ℤ :=
  M.variety.X.left.ord
    (M.data.fieldIso (D.functions (Classical.choose (D.covers (M.map.left p.val))))) p.val

def pulledCombinationCoefficient {P : LogPair k n} (M : BirationalModel P)
    (D : CartierCombination P.variety) (p : PrimePoint M.variety) : ℝ :=
  ∑ i, D.coefficients i * (pulledCartierCoefficient M (D.components i) p : ℝ)

/-- The log discrepancy of a prime divisor $p$ on a birational model `M` of the log pair $P$: one
plus the coefficient at $p$ of the canonical divisor of the model (the divisor of the pulled-back
rational top form in `M.data.canonical`), minus the coefficient at $p$ of the pullback of the
adjoint Cartier combination of $P$, which represents $K + \Delta$. -/
def logDiscrepancy {P : LogPair k n} (M : BirationalModel P) (p : PrimePoint M.variety) : ℝ :=
  1 + (canonicalDivisor M.data.canonical p : ℝ) - pulledCombinationCoefficient M P.adjoint p

/-- Kawamata log terminal: every prime divisor on every proper birational
normal model has positive log discrepancy. The model calculus is part of the
definition, so every such model carries the comparison data `BirationalData`
and none is omitted from the quantifier (if the calculus fails, the predicate is
false rather than vacuous). The log discrepancy does not depend on the chosen
data: frames change by local units, which have order zero. -/
def IsKlt (P : LogPair k n) : Prop :=
  HasModelCalculus P ∧
    ∀ M : BirationalModel P, ∀ p : PrimePoint M.variety, 0 < logDiscrepancy M p

/-- Log canonical: as `IsKlt`, with nonnegative log discrepancies. -/
def IsLogCanonical (P : LogPair k n) : Prop :=
  HasModelCalculus P ∧
    ∀ M : BirationalModel P, ∀ p : PrimePoint M.variety, 0 ≤ logDiscrepancy M p

theorem IsKlt.isLogCanonical {P : LogPair k n} (h : IsKlt P) : IsLogCanonical P :=
  ⟨h.1, fun M p ↦ (h.2 M p).le⟩

def valuationOnBase {P : LogPair k n} (M : BirationalModel P) (p : PrimePoint M.variety)
    (a : (FunctionField P.variety)ˣ) : ℤ :=
  M.variety.X.left.ord (M.data.fieldIso a) p.val

/-- Q-factoriality uses actual Cartier-line representatives of multiples
of every finite integral Weil divisor. -/
def IsQFactorial (V : NormalVariety k n) : Prop :=
  ∀ D : IntegerWeil V, ∃ m : ℕ, 0 < m ∧ ∃ C : CartierLine V, C.divisor = m • D

end MathlibExt.AlgebraicGeometry.LogPairs
