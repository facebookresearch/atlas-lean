/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmoothManifoldSingularModels
public import MathlibExt.AlgebraicGeometry.HarmonicChernWeilFormulas

/-!
# Native real de Rham complexes and source-normalized singular integration

The de Rham complex uses the existing actual smooth forms and exterior
derivative. Closed-form classes enter through native kernel cycles and
their native homology quotient. Integration is fixed on every genuine
smooth singular simplex by the actual parameter integral.

Neither a comparison map nor its quasi-isomorphism theorem is supplied
as an unrelated cohomology isomorphism. The native quotient adapter is
normalized on every closed form. Integration and de Rham comparison
theorems remain separately sourced Wanted requests.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RealDeRhamSingularModels

open CategoryTheory Opposite TopologicalSpace
open KahlerClassGeometry ManifoldDifferentialForms SmoothManifoldSingularModels
open ManifoldSingularCohomologyModels HarmonicChernWeilFormulas
open scoped Manifold ContDiff Simplicial

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [ExteriorTheory ℝ (Coordinates n) M]

/-- The actual de Rham cochain complex of smooth real forms in every degree. -/
def realDeRhamComplex : CochainComplex (ModuleCat.{0} ℝ) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of ℝ (GlobalForms ℝ (Coordinates n) M p))
    (fun p => ModuleCat.ofHom (d ℝ (Coordinates n) M p)) (by
      intro p
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro α
      apply Subtype.ext
      exact ExteriorTheory.square_zero p α)

/-- The native cycle associated with this same actual closed form. -/
def closedFormCycles (q : ℕ) :
    ModuleCat.of ℝ (closedForms ℝ (Coordinates n) M ((2 * q + 1) + 1)) ⟶
      (realDeRhamComplex (n := n) (M := M)).cycles ((2 * q + 1) + 1) :=
  (realDeRhamComplex (n := n) (M := M)).liftCycles'
    (ModuleCat.ofHom (closedForms ℝ (Coordinates n) M ((2 * q + 1) + 1)).subtype)
    (((2 * q + 1) + 1) + 1) rfl (by
      simp only [realDeRhamComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro α
      change d ℝ (Coordinates n) M ((2 * q + 1) + 1) α.val = 0
      exact α.property)

/-- The native quotient adapter fixes the homology class of every actual closed form. -/
structure EvenDeRhamQuotientSource (q : ℕ) where
  iso : ModuleCat.of ℝ (EvenDeRham (n := n) (M := M) q) ≅
    (realDeRhamComplex (n := n) (M := M)).homology ((2 * q + 1) + 1)
  normalized : ∀ α : closedForms ℝ (Coordinates n) M ((2 * q + 1) + 1),
    iso.hom.hom ((LinearMap.range (dToClosed ℝ (Coordinates n) M (2 * q + 1))).mkQ α) =
      ((realDeRhamComplex (n := n) (M := M)).homologyπ ((2 * q + 1) + 1)).hom
        ((closedFormCycles (n := n) (M := M) q).hom α)

variable [SmoothSingularSource (n := n) (M := M)]

/-- Integration is a cochain map fixed on the actual native generators of all smooth singular cochains. -/
structure SingularIntegrationSource where
  map : realDeRhamComplex (n := n) (M := M) ⟶ smoothSingularCochains (n := n) (M := M) ℝ
  normalized : ∀ (p : ℕ) (α : GlobalForms ℝ (Coordinates n) M p)
    (σ : (smoothSingularSet (n := n) (M := M)) _⦋p⦌),
      smoothCochainValue (n := n) ℝ p ((map.f p).hom α) σ =
        integrateSmoothSimplex (n := n) p α σ

/-- The even de Rham class is sent by the actual native integration cochain map. -/
def integratedEvenClass (I : SingularIntegrationSource (n := n) (M := M))
    (q : ℕ) (Q : EvenDeRhamQuotientSource (n := n) (M := M) q) :
    ModuleCat.of ℝ (EvenDeRham (n := n) (M := M) q) ⟶
      (smoothSingularCochains (n := n) (M := M) ℝ).homology ((2 * q + 1) + 1) :=
  Q.iso.hom ≫ HomologicalComplex.homologyMap I.map ((2 * q + 1) + 1)

end MathlibExt.AlgebraicGeometry.RealDeRhamSingularModels
