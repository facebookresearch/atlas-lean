/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Code.Inequalities.PerOrbitCardClose

open Finset MeasureTheory
open scoped NNReal FinsetFamily

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]




















theorem rmr_perOrbitCard_iff_slabCard (A B : Set (ConfigSpace α)) :
    PerOrbitCard A B ↔ poc_SlabCard A B := by
  unfold PerOrbitCard poc_SlabCard
  refine forall_congr' (fun k => ?_)
  rw [poc_card_boxOrbit A B k, poc_card_imgOrbit A B k]



theorem rmr_slabCard_of_perOrbitCard {A B : Set (ConfigSpace α)}
    (h : PerOrbitCard A B) : poc_SlabCard A B :=
  (rmr_perOrbitCard_iff_slabCard A B).mp h



theorem rmr_perOrbitCard_of_slabCard {A B : Set (ConfigSpace α)}
    (h : poc_SlabCard A B) : PerOrbitCard A B :=
  (rmr_perOrbitCard_iff_slabCard A B).mpr h









theorem rmr_swapInjection_iff_slabCard (A B : Set (ConfigSpace α)) :
    r2k_SwapInjection A B ↔ poc_SlabCard A B :=
  (r2k_swapInjection_iff_perOrbitCard A B).trans (rmr_perOrbitCard_iff_slabCard A B)









theorem rmr_slabCard_rbi : poc_SlabCard rbi_A rbi_B :=
  rmr_slabCard_of_perOrbitCard perOrbitCard_rbi


theorem rmr_slabCard_of_disjoint_support_po {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    poc_SlabCard A B :=
  rmr_slabCard_of_perOrbitCard (perOrbitCard_of_disjoint_support hA hB hST)


theorem rmr_slabCard_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : poc_SlabCard A B :=
  rmr_slabCard_of_perOrbitCard (perOrbitCard_of_box_empty hbox)






theorem rmr_reimer_wprob_of_slabCard (φ : α → Bool → ℝ) (hφ0 : ∀ x b, 0 ≤ φ x b)
    (hφ1 : ∀ x, φ x false + φ x true = 1) {A B : Set (ConfigSpace α)}
    (h : poc_SlabCard A B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B :=
  reimer_wprob_of_perOrbitCard φ hφ0 hφ1 (rmr_perOrbitCard_of_slabCard h)

end StatMech.Walls
