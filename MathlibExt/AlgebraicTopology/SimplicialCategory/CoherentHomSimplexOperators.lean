/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomSimplex
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMaximumNerveOperators

/-!
# Actual operators and strict maps on original Hom simplices

The last-front maximum construction follows the actual right join
operator. The resulting enriched simplices retain the original source
and target, and commute with strict enriched postcomposition.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomSimplexOperators
open SimplicialEnrichment HomSimplex PathMaximumOperators MaximumNerveOperators
variable {C D : Carrier.{u}} {n m : ℕ} (x y : C)

/-- The actual whole last-Hom map commutes with the supplied original front simplex operator. -/
theorem lastMap_naturality (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (τ : (Δ[m] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y)) (i : Fin (n + 1)) :
    nerveMap (imageFunctor θ i) ≫ lastMap x y τ (θ.toOrderHom i) =
      lastMap x y (SSet.stdSimplex.map θ ≫ τ) i :=
  maximumMap_postcompose τ θ i

/-- The original source/target object assignment follows the actual right join operator. -/
theorem object_naturality (θ : ⦋n⦌ ⟶ ⦋m⦌) (a : Fin (n + 2)) :
    HomSimplex.object x y ((extension θ).toOrderHom a) = HomSimplex.object x y a := by
  cases a using Fin.lastCases with
  | last => rw [extension_last]; simp only [HomSimplex.object_last]
  | cast i => rw [extension_front]; simp only [HomSimplex.object_front]

/-- The actual last-Hom construction follows every supplied strict enriched Hom map. -/
theorem lastMap_postcompose (F : C ⟶ D)
    (τ : (Δ[n] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y)) (i : Fin (n + 1)) :
    lastMap x y τ i ≫ F.map x y = lastMap (F.obj x) (F.obj y) (τ ≫ F.map x y) i := by
  exact Category.assoc _ _ _

end CategoryTheory.CoherentRealization.HomSimplexOperators
