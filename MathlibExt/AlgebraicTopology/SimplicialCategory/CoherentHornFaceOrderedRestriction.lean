/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornFirstFaceIntervals
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornLastFaceIntervals
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornEndpointFaceReadback

/-!
# Actual ordered nonexceptional Hom restriction to every supplied face

The supplied first and last interval equations apply to every original
ordered interval whose ambient endpoints are not the exceptional outer
pair. The two endpoint faces read themselves back through their genuine
whole Hom isomorphisms.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornFaceOrderedRestriction
open SimplicialEnrichment
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))

/-- Every original supplied face interval reads exactly its whole actual face Hom map whenever its ordered
  ambient endpoints are nonexceptional. -/
theorem restriction (k : Fin (n + 3)) (hk : k ≠ i) (a b : Fin (n + 2)) (hab : a ≤ b)
    (h : k.succAbove a ≠ 0 ∨ k.succAbove b ≠ Fin.last (n + 2)) :
    (coherentSimplexMap (SimplexCategory.δ k)).map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫
      HornOrderedMaps.orderedMap f hi₀ hiₙ (k.succAbove a) (k.succAbove b)
        ((Fin.succAboveOrderEmb k).monotone hab) h =
      HornHomFaces.faceMap f k hk (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) := by
  classical
  have hAB : k.succAbove a ≤ k.succAbove b := (Fin.succAboveOrderEmb k).monotone hab
  by_cases ha₀ : k.succAbove a = 0
  · have hbₙ : k.succAbove b ≠ Fin.last (n + 2) := h.resolve_left (not_not_intro ha₀)
    have haₙ : k.succAbove a ≠ Fin.last (n + 2) := ne_of_lt (lt_of_le_of_lt hAB (Fin.lt_last_iff_ne_last.mpr hbₙ))
    rw [HornOrderedMaps.map_eq_last f hi₀ hiₙ (k.succAbove a) (k.succAbove b) hAB h haₙ hbₙ]
    by_cases hkₙ : k = Fin.last (n + 2)
    · subst k
      exact HornEndpointFaceReadback.last f hiₙ a b
    · have ha : a ≠ Fin.last (n + 1) := fun ht => haₙ ((congrArg k.succAbove ht).trans (Fin.succAbove_ne_last_last hkₙ))
      have hb : b ≠ Fin.last (n + 1) := fun ht => hbₙ ((congrArg k.succAbove ht).trans (Fin.succAbove_ne_last_last hkₙ))
      exact HornLastFaceIntervals.restriction f hiₙ k hkₙ hk a b ha hb
  · have hb₀ : k.succAbove b ≠ 0 := fun ht => ha₀ (le_antisymm (ht ▸ hAB) (Fin.zero_le _))
    rw [HornOrderedMaps.map_eq_first f hi₀ hiₙ (k.succAbove a) (k.succAbove b) hAB h ha₀ hb₀]
    by_cases hk₀ : k = 0
    · subst k
      exact HornEndpointFaceReadback.first f hi₀ a b
    · have ha : a ≠ 0 := fun ht => ha₀ ((congrArg k.succAbove ht).trans (Fin.succAbove_ne_zero_zero hk₀))
      have hb : b ≠ 0 := fun ht => hb₀ ((congrArg k.succAbove ht).trans (Fin.succAbove_ne_zero_zero hk₀))
      exact HornFirstFaceIntervals.restriction f hi₀ k hk₀ hk a b ha hb

end CategoryTheory.CoherentRealization.HornFaceOrderedRestriction
