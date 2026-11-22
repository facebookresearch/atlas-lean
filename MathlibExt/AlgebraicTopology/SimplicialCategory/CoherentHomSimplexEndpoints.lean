/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFrontRestriction
import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSlice

/-!
# Actual fixed endpoint restrictions of original Hom simplices

The entire front enriched simplex is the supplied source identity and
the last enriched vertex is the supplied target. Transport through the
actual join-standard-simplex isomorphism therefore gives a genuine
right mapping-space simplex, retaining the same individual objects.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomSimplexEndpoints
open SimplicialEnrichment HomSimplex
variable {C : Carrier.{u}} {n : ℕ} (x y : C) (τ : (Δ[n] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y))

/-- The actual coherent-nerve vertex map of the supplied individual original object. -/
def vertex (x : C) : (Δ[0] : SSet.{u}) ⟶ coherentNerveFunctor.obj C :=
  SSet.yonedaEquiv.symm (constantSimplex C ⦋0⦌ x)

/-- The entire original front restriction is the constant enriched simplex at the supplied source. -/
theorem front_simplex : coherentSimplexMap (SimplexCategory.δ (Fin.last (n + 1))) ≫ simplex x y τ =
    constantSimplex C ⦋n⦌ x := by
  exact HomFrontRestriction.front x y τ ⦋n⦌ _ (fun a => a.as.down) (fun a => Fin.succAbove_last_apply _)

/-- The actual entire last vertex of the coherent simplex is the supplied original target. -/
theorem last_simplex : coherentSimplexMap (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌) ≫ simplex x y τ =
    constantSimplex C ⦋0⦌ y := by
  apply (verticesEquiv C).injective
  change _ = y
  exact (congrArg (HomSimplex.object x y) (SSet.inr'_toOrderHom_zero n)).trans (object_last x y)

/-- The actual front-standard-simplex inclusion reads the supplied source vertex constantly. -/
theorem front_map : SSet.frontInclusion n ≫ SSet.yonedaEquiv.symm (simplex x y τ) =
    SSet.toDeltaZero (Δ[n] : SSet.{u}) ≫ vertex x := by
  have hF := front_simplex x y τ
  have hY := SSet.stdSimplex.δ_comp_yonedaEquiv_symm (X := coherentNerveFunctor.obj C)
    (simplex x y τ) (Fin.last (n + 1))
  have hT : SSet.toDeltaZero (Δ[n] : SSet.{u}) ≫ vertex x =
      SSet.yonedaEquiv.symm (constantSimplex C ⦋n⦌ x) := by
    apply SSet.yonedaEquiv.injective
    change _ = _
    rfl
  exact (congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1] => f ≫ (SSet.yonedaEquiv (X :=
    coherentNerveFunctor.obj C) (n := ⦋n + 1⦌)).symm (simplex x y τ)) (SSet.frontInclusion_eq n)).trans
    (hY.trans ((congrArg (fun σ => SSet.yonedaEquiv.symm σ) hF).trans hT.symm))

/-- The actual right-standard-simplex vertex reads the supplied target vertex. -/
theorem right_map : SSet.rightVertex n ≫ SSet.yonedaEquiv.symm (simplex x y τ) = vertex y := by
  have hY := SSet.yonedaEquiv_symm_naturality_left (X := coherentNerveFunctor.obj C)
    (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌) (simplex x y τ)
  exact (congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ Δ[n + 1] => f ≫ (SSet.yonedaEquiv (X :=
    coherentNerveFunctor.obj C) (n := ⦋n + 1⦌)).symm (simplex x y τ)) (SSet.rightVertex_eq n)).trans
    (hY.trans (congrArg (fun σ => SSet.yonedaEquiv.symm σ) (last_simplex x y τ)))

/-- The genuine right mapping-space simplex constructed from the supplied original Hom simplex. -/
def mappingSimplex : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋n⦌ :=
  (SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n).symm
    ⟨SSet.yonedaEquiv.symm (simplex x y τ), front_map x y τ, right_map x y τ⟩

/-- The constructed mapping simplex reads back the entire original enriched simplex under the actual join transport. -/
theorem mappingSimplex_readback :
    ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) (mappingSimplex x y τ)).val = SSet.yonedaEquiv.symm
      (simplex x y τ) := by
  exact congrArg Subtype.val ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n).apply_symm_apply _)

end CategoryTheory.CoherentRealization.HomSimplexEndpoints
