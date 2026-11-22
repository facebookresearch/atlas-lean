/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRawRightMappingEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceKanW

/-!
# Original right-mapping simplices of a standard simplex

The full original successor map is determined by its constant front
and its same final endpoint. Every original front vertex is retained;
the statement uses the actual native standard-simplex order maps.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

/-- The literal original endpoint map at the supplied ambient ordinal vertex. -/
def simplexVertex (n : ℕ) (i : Fin (n + 1)) : (Δ[0] : SSet.{u}) ⟶ Δ[n] :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)

private theorem standardMap_readback {n m : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    f = SSet.stdSimplex.map (SSet.stdSimplex.objEquiv (SSet.yonedaEquiv f)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_map, Equiv.symm_apply_apply]

/-- The same original successor's full front evaluation is precisely its original fixed source vertex. -/
theorem simplex_successor_front {n m : ℕ} (a b : Fin (n + 1))
    (σ : (SSet.mappingSpaceRight (Δ[n] : SSet.{u}) (simplexVertex n a) (simplexVertex n b)) _⦋m⦌)
    (i : Fin (m + 1)) :
    (SSet.stdSimplex.objEquiv (SSet.yonedaEquiv (successor (simplexVertex n a) (simplexVertex n b) σ))).toOrderHom
      i.castSucc = a := by
  have h := (SSet.mappingSpaceRight.simplexEquivSucc (Δ[n] : SSet.{u})
    (simplexVertex n a) (simplexVertex n b) m σ).property.1
  change SSet.frontInclusion m ≫ successor (simplexVertex n a) (simplexVertex n b) σ =
    SSet.toDeltaZero (Δ[m] : SSet.{u}) ≫ simplexVertex n a at h
  rw [SSet.frontInclusion_eq] at h
  let φ := SSet.stdSimplex.objEquiv (SSet.yonedaEquiv (successor (simplexVertex n a) (simplexVertex n b) σ))
  have hφ := standardMap_readback (successor (simplexVertex n a) (simplexVertex n b) σ)
  have he := congrArg SSet.yonedaEquiv
    ((congrArg (fun f => SSet.stdSimplex.δ (Fin.last (m + 1)) ≫ f) hφ).symm.trans h)
  change SSet.yonedaEquiv
    (SSet.stdSimplex.map (SimplexCategory.δ (Fin.last (m + 1))) ≫ SSet.stdSimplex.map φ) = _ at he
  rw [← SSet.stdSimplex.map_comp, SSet.yonedaEquiv_map] at he
  apply_fun (fun x : (Δ[n] : SSet.{u}) _⦋m⦌ => x i) at he
  change (SSet.stdSimplex.objEquiv (SSet.yonedaEquiv (successor (simplexVertex n a) (simplexVertex n b) σ))).toOrderHom
      ((Fin.last (m + 1)).succAbove i) = _ at he
  rw [Fin.succAbove_last_apply] at he
  exact he.trans (by
    have ht := SSet.toDeltaZero_eq (SSet.stdSimplex.map (SimplexCategory.const ⦋m⦌ ⦋0⦌ 0))
    have hc : SSet.toDeltaZero (Δ[m] : SSet.{u}) ≫ simplexVertex n a =
        SSet.stdSimplex.map (SimplexCategory.const ⦋m⦌ ⦋n⦌ a) :=
      (congrArg (fun f => f ≫ simplexVertex n a) ht.symm).trans
        (SSet.stdSimplex.map_comp (SimplexCategory.const ⦋m⦌ ⦋0⦌ 0)
          (SimplexCategory.const ⦋0⦌ ⦋n⦌ a)).symm
    exact congrArg (fun x : (Δ[n] : SSet.{u}) _⦋m⦌ => x i)
      ((congrArg SSet.yonedaEquiv hc).trans (SSet.yonedaEquiv_map _)))

/-- The same original successor's last vertex is precisely its full original target vertex. -/
theorem simplex_successor_last {n m : ℕ} (a b : Fin (n + 1))
    (σ : (SSet.mappingSpaceRight (Δ[n] : SSet.{u}) (simplexVertex n a) (simplexVertex n b)) _⦋m⦌) :
    (SSet.stdSimplex.objEquiv (SSet.yonedaEquiv (successor (simplexVertex n a) (simplexVertex n b) σ))).toOrderHom
      (Fin.last (m + 1)) = b := by
  have h := (SSet.mappingSpaceRight.simplexEquivSucc (Δ[n] : SSet.{u})
    (simplexVertex n a) (simplexVertex n b) m σ).property.2
  change SSet.rightVertex m ≫ successor (simplexVertex n a) (simplexVertex n b) σ = simplexVertex n b at h
  rw [SSet.rightVertex_eq] at h
  let φ := SSet.stdSimplex.objEquiv (SSet.yonedaEquiv (successor (simplexVertex n a) (simplexVertex n b) σ))
  have hφ := standardMap_readback (successor (simplexVertex n a) (simplexVertex n b) σ)
  have he := congrArg SSet.yonedaEquiv
    ((congrArg (fun f => SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋m⦌ ⦋0⦌) ≫ f) hφ).symm.trans h)
  rw [← SSet.stdSimplex.map_comp, SSet.yonedaEquiv_map] at he
  have hv := congrArg (fun x : (Δ[n] : SSet.{u}) _⦋0⦌ => x 0) he
  change (SSet.stdSimplex.objEquiv (SSet.yonedaEquiv (successor (simplexVertex n a) (simplexVertex n b) σ))).toOrderHom
      ((AugmentedSimplexCategory.inr' ⦋m⦌ ⦋0⦌).toOrderHom 0) = _ at hv
  rw [SSet.inr'_toOrderHom_zero] at hv
  exact hv

/-- Both full original front and last equations determine the same whole original right-mapping simplex. -/
theorem simplex_mapping_subsingleton {n m : ℕ} (a b : Fin (n + 1)) :
    Subsingleton ((SSet.mappingSpaceRight (Δ[n] : SSet.{u}) (simplexVertex n a) (simplexVertex n b)) _⦋m⦌) := by
  constructor
  intro σ τ
  apply (SSet.mappingSpaceRight.simplexEquivSucc (Δ[n] : SSet.{u})
    (simplexVertex n a) (simplexVertex n b) m).injective
  apply Subtype.ext
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  ext i
  by_cases hi : i = Fin.last (m + 1)
  · subst i
    exact congrArg Fin.val ((simplex_successor_last a b σ).trans (simplex_successor_last a b τ).symm)
  · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    exact congrArg Fin.val ((simplex_successor_front a b σ j).trans (simplex_successor_front a b τ j).symm)

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
