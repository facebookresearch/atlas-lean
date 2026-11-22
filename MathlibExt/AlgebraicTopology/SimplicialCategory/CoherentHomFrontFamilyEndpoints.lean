/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFrontFamilyRestriction
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomSimplexEndpoints

/-!
# Literal endpoints of actual front-compatible Hom families

Every genuine original last-interval family produces an actual right
mapping simplex. Its entire front and original last vertex are the
specified individual source and target. All equations are proved on
the original enriched maps and actual join operators.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomFrontFamilyEndpoints
open SimplicialEnrichment HomFrontFamily
variable {C : Carrier.{u}} {n : ℕ} (x y : C) (family : Family x y n)

/-- The entire original front restriction is the constant enriched simplex at the supplied source. -/
theorem front_simplex : coherentSimplexMap (SimplexCategory.δ (Fin.last (n + 1))) ≫ simplex x y family =
    constantSimplex C ⦋n⦌ x := by
  exact HomFrontFamilyRestriction.front x y family ⦋n⦌ _ (fun a => a.as.down) (fun a => Fin.succAbove_last_apply _)

/-- The actual entire last vertex of the coherent simplex is the supplied original target. -/
theorem last_simplex : coherentSimplexMap (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌) ≫ simplex x y family =
    constantSimplex C ⦋0⦌ y := by
  apply (verticesEquiv C).injective
  change _ = y
  exact (congrArg (HomFrontFamily.object x y) (SSet.inr'_toOrderHom_zero n)).trans (object_last x y)

/-- The actual front-standard-simplex inclusion reads the supplied source vertex constantly. -/
theorem front_map : SSet.frontInclusion n ≫ SSet.yonedaEquiv.symm (simplex x y family) =
    SSet.toDeltaZero (Δ[n] : SSet.{u}) ≫ HomSimplexEndpoints.vertex x := by
  have hF := front_simplex x y family
  have hY := SSet.stdSimplex.δ_comp_yonedaEquiv_symm (X := coherentNerveFunctor.obj C)
    (simplex x y family) (Fin.last (n + 1))
  have hT : SSet.toDeltaZero (Δ[n] : SSet.{u}) ≫ HomSimplexEndpoints.vertex x =
      SSet.yonedaEquiv.symm (constantSimplex C ⦋n⦌ x) := by
    apply SSet.yonedaEquiv.injective
    rfl
  exact (congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1] => f ≫ (SSet.yonedaEquiv (X :=
    coherentNerveFunctor.obj C) (n := ⦋n + 1⦌)).symm (simplex x y family)) (SSet.frontInclusion_eq n)).trans
    (hY.trans ((congrArg (fun σ => SSet.yonedaEquiv.symm σ) hF).trans hT.symm))

/-- The actual right-standard-simplex vertex reads the supplied target vertex. -/
theorem right_map : SSet.rightVertex n ≫ SSet.yonedaEquiv.symm (simplex x y family) = HomSimplexEndpoints.vertex y := by
  have hY := SSet.yonedaEquiv_symm_naturality_left (X := coherentNerveFunctor.obj C)
    (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌) (simplex x y family)
  exact (congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ Δ[n + 1] => f ≫ (SSet.yonedaEquiv (X :=
    coherentNerveFunctor.obj C) (n := ⦋n + 1⦌)).symm (simplex x y family)) (SSet.rightVertex_eq n)).trans
    (hY.trans (congrArg (fun σ => SSet.yonedaEquiv.symm σ) (last_simplex x y family)))

/-- The genuine right mapping-space simplex constructed from the supplied original Hom simplex. -/
def mappingSimplex : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
    (HomSimplexEndpoints.vertex y)) _⦋n⦌ :=
  (SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n).symm
    ⟨SSet.yonedaEquiv.symm (simplex x y family), front_map x y family, right_map x y family⟩

/-- The constructed mapping simplex reads back the entire original enriched simplex under the actual join transport. -/
theorem mappingSimplex_readback :
    ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) (mappingSimplex x y family)).val =
      SSet.yonedaEquiv.symm (simplex x y family) := by
  exact congrArg Subtype.val ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n).apply_symm_apply _)


end CategoryTheory.CoherentRealization.HomFrontFamilyEndpoints
