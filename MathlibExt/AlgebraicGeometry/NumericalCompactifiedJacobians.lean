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
subschemes whose image is a union of irreducible components. Stability
uses Euler characteristic of the universal torsion-free quotient of the
restriction to each proper nonempty subcurve.

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

/-- Quasi-coherence and finite generation on affine opens. -/
def IsCoherent {X : Scheme.{u}} (F : X.Modules) : Prop :=
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

/-- The canonical torsion-free quotient is characterized by its universal property. -/
structure TorsionFreeQuotient {Z : Scheme.{u}} (F : Z.Modules) where
  Q : Z.Modules
  q : F ⟶ Q
  [epi : Epi q]
  coherent : IsCoherent Q
  torsionFree : IsTorsionFree Q
  universal : ∀ (N : Z.Modules), IsCoherent N → IsTorsionFree N →
    ∀ f : F ⟶ N, ∃! g : Q ⟶ N, q ≫ g = f

/-- Canonically characterized restrictions to the actual proper subcurves. -/
class TorsionFreeRestrictions (C : Scheme.{u}) where
  restriction : ∀ (F : C.Modules), IsCoherent F → ∀ Y : Subcurve C,
    TorsionFreeQuotient ((Scheme.Modules.pullback Y.i).obj F)

/-- A rational polarization indexed by the actual curve components. -/
abbrev Polarization (C : Scheme.{u}) := Component C →₀ ℚ

/-- Total weight is the finite component sum. -/
def totalWeight {C : Scheme.{u}} (q : Polarization C) : ℚ := q.sum fun _ a ↦ a

/-- Weight of a subcurve is the sum over components lying in its image. -/
def subcurveWeight {C : Scheme.{u}} (q : Polarization C) (Y : Subcurve C) : ℚ := by
  classical
  exact q.sum fun c a ↦ if c.val ⊆ Set.range Y.i then a else 0

/-- Euler characteristic from actual coherent cohomology. -/
def euler {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (F : X.Modules) : ℤ :=
  (Module.finrank k (cohomology f F 0) : ℤ) -
    Module.finrank k (cohomology f F 1)

/-- Esteves/MRV semistability, on actual rank-one torsion-free sheaves. -/
def IsSemistable {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [TorsionFreeRestrictions C.left] (q : Polarization C.left) (F : C.left.Modules) : Prop :=
  IsCoherent F ∧ IsTorsionFree F ∧ HasGenericRankOne F ∧
    (euler C.hom F : ℚ) = totalWeight q ∧
    ∀ (Y : Subcurve C.left) (hF : IsCoherent F),
      subcurveWeight q Y ≤
        (euler (Y.i ≫ C.hom) (TorsionFreeRestrictions.restriction F hF Y).Q : ℚ)

/-- Stability uses the strict subcurve inequalities. -/
def IsStable {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [TorsionFreeRestrictions C.left] (q : Polarization C.left) (F : C.left.Modules) : Prop :=
  IsCoherent F ∧ IsTorsionFree F ∧ HasGenericRankOne F ∧
    (euler C.hom F : ℚ) = totalWeight q ∧
    ∀ (Y : Subcurve C.left) (hF : IsCoherent F),
      subcurveWeight q Y <
        (euler (Y.i ≫ C.hom) (TorsionFreeRestrictions.restriction F hF Y).Q : ℚ)

/-- Nondegeneracy compares only semistable sheaves to stable sheaves. -/
def IsNondegenerate {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [TorsionFreeRestrictions C.left] (q : Polarization C.left) : Prop :=
  ∀ F : C.left.Modules, IsSemistable C q F → IsStable C q F

/-- A marking is witnessed to lie in an actual smooth open neighborhood. -/
structure SmoothMarking {k : Type u} [Field k] (C : Over (Spec (.of k))) where
  p : 𝟙_ (Over (Spec (.of k))) ⟶ C
  U : C.left.Opens
  smooth : Smooth (U.ι ≫ C.hom)
  lift : 𝟙_ (Over (Spec (.of k))) ⟶ Over.mk (U.ι ≫ C.hom)
  factors : lift ≫ Over.homMk U.ι = p

/-- Families over finite-type test schemes, with the actual closed-fiber stability test. -/
def IsStableFamily {k : Type u} [Field k] (C T : Over (Spec (.of k)))
    [TorsionFreeRestrictions C.left] (q : Polarization C.left)
    (F : (prod C T).left.Modules) : Prop :=
  IsCoherent F ∧ IsFlatOver (prod.snd : prod C T ⟶ T).left F ∧
    ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ T,
      IsStable C q ((Scheme.Modules.pullback (pointSection C T x).left).obj F)

/-- A fine moduli representative with a normalized actual universal sheaf. -/
structure FineCompactifiedJacobian {k : Type u} [Field k]
    (C : Over (Spec (.of k))) [TorsionFreeRestrictions C.left]
    (q : Polarization C.left) (s : SmoothMarking C) where
  J : Over (Spec (.of k))
  [proper : IsProper J.hom]
  [reduced : IsReduced J.left]
  [connected : ConnectedSpace J.left]
  dimension : topologicalKrullDim J.left = genus C.hom
  F : (prod C J).left.Modules
  stableFamily : IsStableFamily C J q F
  normalized : IsNormalized C J s.p F
  universal : ∀ (T : Over (Spec (.of k))),
    LocallyOfFiniteType T.hom → QuasiCompact T.hom →
      ∀ G : (prod C T).left.Modules, IsStableFamily C T q G →
        IsNormalized C T s.p G →
          ∃! f : T ⟶ J, Nonempty (familyPullback C J T F f ≅ G)

end MathlibExt.AlgebraicGeometry.NumericalCompactifiedJacobians
