/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornMiddleMap
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOutsideFaceAlgebra

/-!
# Whole composition of the actual short Hom maps of an inner horn

The supplied first and last faces preserve original enriched composition.
Their middle Hom maps are equal by the actual common-face relation, so
both short-leg equations use the same whole original middle map.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornShortComposition
open SimplicialEnrichment HornBoxFaces
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) (b c : Interior.{u} n)

private theorem last_outside (b : Interior.{u} n) :
    (OrdinalFace.embedding (Fin.last (n + 2))) (ULift.up ((HornBoxFaces.vertex b).castPred (vertex_ne_last b))) <
      (ULift.up (Fin.last (n + 2)) : ULift.{u} (Fin (n + 3))) := by
  change (Fin.last (n + 2)).succAbove ((HornBoxFaces.vertex b).castPred (vertex_ne_last b)) < Fin.last (n + 2)
  simpa only [Fin.succAbove_last, Fin.castSucc_castPred] using (show HornBoxFaces.vertex b < Fin.last (n +
    2) from b.property.2)

private theorem first_outside (b : Interior.{u} n) :
    (ULift.up (0 : Fin (n + 3)) : ULift.{u} (Fin (n + 3))) <
      (OrdinalFace.embedding (0 : Fin (n + 3))) (ULift.up ((HornBoxFaces.vertex b).pred (vertex_ne_zero b))) := by
  change (0 : Fin (n + 3)) < (0 : Fin (n + 3)).succAbove ((HornBoxFaces.vertex b).pred (vertex_ne_zero b))
  simpa only [Fin.succAbove_zero, Fin.succ_pred] using (show (0 : Fin (n + 3)) < HornBoxFaces.vertex b from
    b.property.1)

/-- The original left short-leg union is mapped to actual target composition using the same whole middle Hom map. -/
theorem left_comp :
    CompositionFace.composition (ULift.up.{u} (0 : Fin (n + 3))) b.val c.val ≫ leftMap f hi₀ hiₙ c =
      (leftMap f hi₀ hiₙ b ⊗ₘ HornMiddleMap.firstMap f hi₀ b c) ≫
        eComp SSet.{u} (HornFaces.object f 0) (HornFaces.object f (HornBoxFaces.vertex b))
          (HornFaces.object f (HornBoxFaces.vertex c)) := by
  rw [HornMiddleMap.firstMap_eq_lastMap f hi₀ hiₙ b c,
    HornShortLegs.leftMap_eq_lastFace f hi₀ hiₙ b, HornShortLegs.leftMap_eq_lastFace f hi₀ hiₙ c]
  dsimp only [HornMiddleMap.lastMap]
  exact OutsideFaceAlgebra.faceMap_comp f (Fin.last (n + 2)) hiₙ.symm
    (ULift.up (0 : Fin (n + 2))) (ULift.up ((HornBoxFaces.vertex b).castPred (vertex_ne_last b)))
    (ULift.up ((HornBoxFaces.vertex c).castPred (vertex_ne_last c)))
    (Or.inr (last_outside b)) (Or.inr (last_outside c)) (Or.inr (last_outside c))
    (by rw [Fin.succAbove_last]; rfl)
    (by simpa only [Fin.succAbove_last] using Fin.castSucc_castPred (HornBoxFaces.vertex b) (vertex_ne_last b))
    (by simpa only [Fin.succAbove_last] using Fin.castSucc_castPred (HornBoxFaces.vertex c) (vertex_ne_last c))

/-- The original right short-leg union is mapped to actual target composition with the same whole middle Hom map. -/
theorem right_comp :
    CompositionFace.composition b.val c.val (ULift.up.{u} (Fin.last (n + 2))) ≫ rightMap f hi₀ hiₙ b =
      (HornMiddleMap.firstMap f hi₀ b c ⊗ₘ rightMap f hi₀ hiₙ c) ≫
        eComp SSet.{u} (HornFaces.object f (HornBoxFaces.vertex b))
          (HornFaces.object f (HornBoxFaces.vertex c)) (HornFaces.object f (Fin.last (n + 2))) := by
  rw [HornShortLegs.rightMap_eq_firstFace f hi₀ hiₙ b, HornShortLegs.rightMap_eq_firstFace f hi₀ hiₙ c]
  dsimp only [HornMiddleMap.firstMap]
  exact OutsideFaceAlgebra.faceMap_comp f 0 hi₀.symm
    (ULift.up ((HornBoxFaces.vertex b).pred (vertex_ne_zero b)))
    (ULift.up ((HornBoxFaces.vertex c).pred (vertex_ne_zero c))) (ULift.up (Fin.last (n + 1)))
    (Or.inl (first_outside b)) (Or.inl (first_outside c)) (Or.inl (first_outside b))
    (Fin.succ_pred (HornBoxFaces.vertex b) (vertex_ne_zero b))
    (Fin.succ_pred (HornBoxFaces.vertex c) (vertex_ne_zero c)) (by rw [Fin.succAbove_zero]; rfl)

end CategoryTheory.CoherentRealization.HornShortComposition
