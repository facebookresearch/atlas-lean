/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Topology.KrullDimension
public import MathlibExt.AlgebraicGeometry.PointedPicardFamilies

@[expose] public noncomputable section

/-!
# Numerical stability for compactified Jacobians

Coherence, torsion freeness, generic rank one, and relative flatness are
conditions on actual module sheaves. Subcurves are actual reduced closed
subschemes whose image is a union of irreducible components. On a proper
curve, stability uses the Euler characteristic `h⁰ - h¹` of the universal
torsion-free quotient of the restriction to each proper nonempty subcurve,
itself a proper curve. Coherent cohomology on a proper curve is
finite-dimensional and vanishes above degree one, so `h⁰ - h¹` with
`Module.finrank` is the actual Euler characteristic.

The moduli problem is stated over an algebraically closed field `k`,
restricted to parameter schemes locally of finite type (the interface does
not classify families over other bases). Families are tested at their
`k`-points: these are exactly the closed points, which are dense in every
closed subset, and stability is an open condition in flat families of
torsion-free rank-one sheaves (Esteves, §3), so this is equivalent to
testing every geometric fiber.

References: E. Esteves, *Compactifying the relative Jacobian over families
of reduced curves*; Melo--Rapagnetta--Viviani, *Fine compactified Jacobians
of reduced curves*, §§2,5. https://arxiv.org/abs/1406.2299
-/

namespace MathlibExt.AlgebraicGeometry.NumericalCompactifiedJacobians

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry TopologicalSpace
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open _root_.MathlibExt.AlgebraicGeometry.PointedPicardFamilies

universe u

/-- Quasi-coherence and finite generation on affine opens: a quasi-coherent sheaf of finite
type. On a locally Noetherian scheme, such as the curves and the families over parameter
schemes of finite type below, this is coherence. -/
def IsFiniteTypeQuasicoherent {X : Scheme.{u}} (F : X.Modules) : Prop :=
  SheafOfModules.IsQuasicoherent F ∧
    ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(F, U)

/-- No nonzero local section is killed by a regular function. -/
def IsTorsionFree {X : Scheme.{u}} (F : X.Modules) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U →
    ∀ a : Γ(X, U), a ∈ nonZeroDivisors Γ(X, U) →
      ∀ s : Γ(F, U), a • s = 0 → s = 0

/-- Rank one at all generic components is dense-open line-bundle triviality. -/
def HasGenericRankOne {X : Scheme.{u}} (F : X.Modules) : Prop :=
  ∃ U : X.Opens, Dense (U : Set X) ∧
    IsLineBundle ((Scheme.Modules.pullback U.ι).obj F)

/-- Relative flatness tested on the actual affine section modules. -/
def IsFlatOver {X S : Scheme.{u}} (q : X ⟶ S) (F : X.Modules) : Prop :=
  ∀ (U : S.Opens) (V : X.Opens), IsAffineOpen U → IsAffineOpen V →
    ∀ e : V ≤ q ⁻¹ᵁ U,
      letI : Module Γ(S, U) Γ(F, V) :=
        Module.compHom Γ(F, V) (q.appLE U V e).hom
      Module.Flat Γ(S, U) Γ(F, V)

/-- Irreducible components, as the actual maximal irreducible closed subsets. -/
abbrev Component (C : Scheme.{u}) :=
  {Z : Set C // Z ∈ irreducibleComponents C}

/-- A proper nonempty reduced subcurve with its genuine closed immersion. -/
structure Subcurve (C : Scheme.{u}) where
  Z : Scheme.{u}
  i : Z ⟶ C
  [closed : IsClosedImmersion i]
  [reduced : IsReduced Z]
  nonempty : Nonempty Z
  dimension : topologicalKrullDim Z = 1
  proper : Set.range i ≠ Set.univ
  components : ∃ S : Finset (Component C),
    Set.range i = ⋃ c ∈ S, c.val

/-- A subcurve of a proper curve is a proper curve. -/
instance Subcurve.isProperCurve {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [IsProperCurve C.hom] (Y : Subcurve C.left) : IsProperCurve (Y.i ≫ C.hom) :=
  haveI := Y.closed
  { toIsProper := inferInstance, topologicalKrullDim_eq_one := Y.dimension }

/-- The canonical torsion-free quotient is characterized by its universal property. -/
structure TorsionFreeQuotient {Z : Scheme.{u}} (F : Z.Modules) where
  Q : Z.Modules
  q : F ⟶ Q
  [epi : Epi q]
  coherent : IsFiniteTypeQuasicoherent Q
  torsionFree : IsTorsionFree Q
  universal : ∀ (N : Z.Modules), IsFiniteTypeQuasicoherent N → IsTorsionFree N →
    ∀ f : F ⟶ N, ∃! g : Q ⟶ N, q ≫ g = f

/-- Canonically characterized restrictions to the actual proper subcurves. -/
class TorsionFreeRestrictions (C : Scheme.{u}) where
  restriction : ∀ (F : C.Modules), IsFiniteTypeQuasicoherent F → ∀ Y : Subcurve C,
    TorsionFreeQuotient ((Scheme.Modules.pullback Y.i).obj F)

/-- A rational polarization indexed by the actual curve components. -/
abbrev Polarization (C : Scheme.{u}) := Component C →₀ ℚ

/-- Total weight is the finite component sum. -/
def totalWeight {C : Scheme.{u}} (q : Polarization C) : ℚ := q.sum fun _ a ↦ a

/-- Weight of a subcurve is the sum over components lying in its image. -/
def subcurveWeight {C : Scheme.{u}} (q : Polarization C) (Y : Subcurve C) : ℚ := by
  classical
  exact q.sum fun c a ↦ if c.val ⊆ Set.range Y.i then a else 0

/-- The Euler characteristic `h⁰(F) - h¹(F)` of a coherent sheaf on a proper curve, from
actual coherent cohomology (finite-dimensional, and zero above degree one). -/
def euler {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProperCurve f] (F : X.Modules)
    (_hF : IsFiniteTypeQuasicoherent F) : ℤ :=
  (Module.finrank k (cohomology f F 0) : ℤ) -
    Module.finrank k (cohomology f F 1)

/-- Esteves/MRV semistability on a proper curve, on actual rank-one torsion-free sheaves. -/
def IsSemistable {k : Type u} [Field k] (C : Over (Spec (.of k))) [IsProperCurve C.hom]
    [TorsionFreeRestrictions C.left] (q : Polarization C.left) (F : C.left.Modules) : Prop :=
  ∃ hF : IsFiniteTypeQuasicoherent F, IsTorsionFree F ∧ HasGenericRankOne F ∧
    (euler C.hom F hF : ℚ) = totalWeight q ∧
    ∀ Y : Subcurve C.left,
      subcurveWeight q Y ≤
        (euler (Y.i ≫ C.hom) (TorsionFreeRestrictions.restriction F hF Y).Q
          (TorsionFreeRestrictions.restriction F hF Y).coherent : ℚ)

/-- Stability uses the strict subcurve inequalities. -/
def IsStable {k : Type u} [Field k] (C : Over (Spec (.of k))) [IsProperCurve C.hom]
    [TorsionFreeRestrictions C.left] (q : Polarization C.left) (F : C.left.Modules) : Prop :=
  ∃ hF : IsFiniteTypeQuasicoherent F, IsTorsionFree F ∧ HasGenericRankOne F ∧
    (euler C.hom F hF : ℚ) = totalWeight q ∧
    ∀ Y : Subcurve C.left,
      subcurveWeight q Y <
        (euler (Y.i ≫ C.hom) (TorsionFreeRestrictions.restriction F hF Y).Q
          (TorsionFreeRestrictions.restriction F hF Y).coherent : ℚ)

/-- Nondegeneracy compares only semistable sheaves to stable sheaves. -/
def IsNondegenerate {k : Type u} [Field k] (C : Over (Spec (.of k))) [IsProperCurve C.hom]
    [TorsionFreeRestrictions C.left] (q : Polarization C.left) : Prop :=
  ∀ F : C.left.Modules, IsSemistable C q F → IsStable C q F

/-- A marking is witnessed to lie in an actual smooth open neighborhood. -/
structure SmoothMarking {k : Type u} [Field k] (C : Over (Spec (.of k))) where
  p : 𝟙_ (Over (Spec (.of k))) ⟶ C
  U : C.left.Opens
  smooth : Smooth (U.ι ≫ C.hom)
  lift : 𝟙_ (Over (Spec (.of k))) ⟶ Over.mk (U.ι ≫ C.hom)
  factors : lift ≫ Over.homMk U.ι = p

/-- The fine moduli problem restricted to parameter schemes locally of finite type over an
algebraically closed field `k` (the test schemes of `FineCompactifiedJacobian.universal`;
the predicate is only stated for them): a flat coherent family whose closed fibers, that
is its fibers at the `k`-points, are stable. By openness of stability this is stability
of every geometric fiber (see the module documentation). -/
def IsStableFamily {k : Type u} [Field k] [IsAlgClosed k] (C T : Over (Spec (.of k)))
    [IsProperCurve C.hom] [LocallyOfFiniteType T.hom] [TorsionFreeRestrictions C.left]
    (q : Polarization C.left) (F : (prod C T).left.Modules) : Prop :=
  IsFiniteTypeQuasicoherent F ∧ IsFlatOver (prod.snd : prod C T ⟶ T).left F ∧
    ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ T,
      IsStable C q ((Scheme.Modules.pullback (pointSection C T x).left).obj F)

/-- A fine moduli representative with a normalized actual universal sheaf, for a proper
curve over an algebraically closed field: it represents the moduli functor of stable
normalized families restricted to parameter schemes locally of finite type and
quasi-compact over `k`. Its dimension is `dim H¹(C, 𝒪_C)`, the arithmetic genus of a
curve with `H⁰(C, 𝒪_C) = k` (such as a connected reduced one). -/
structure FineCompactifiedJacobian {k : Type u} [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [IsProperCurve C.hom]
    [TorsionFreeRestrictions C.left] (q : Polarization C.left) (s : SmoothMarking C) where
  J : Over (Spec (.of k))
  [proper : IsProper J.hom]
  [reduced : IsReduced J.left]
  [connected : ConnectedSpace J.left]
  dimension : topologicalKrullDim J.left =
    Module.finrank k (cohomology C.hom (structureModule C.left) 1)
  F : (prod C J).left.Modules
  stableFamily : IsStableFamily C J q F
  normalized : IsNormalized C J s.p F
  universal : ∀ (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    (G : (prod C T).left.Modules), IsStableFamily C T q G → IsNormalized C T s.p G →
      ∃! f : T ⟶ J, Nonempty (familyPullback C J T F f ≅ G)

end MathlibExt.AlgebraicGeometry.NumericalCompactifiedJacobians
