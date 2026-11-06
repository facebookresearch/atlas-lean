/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOddMarkingData

/-! The compact marker masks are exactly membership in the displayed preferred odd labels. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Literal union of the displayed marking bits at a fixed physical coordinate. -/
def generatedNinthOddMarkerMaskFold (i : Fin 24) : ℕ :=
  (List.finRange 128).foldr (fun k m =>
    (if (generatedNinthOddMarkingLabel k).2 = i then
      2 ^ (generatedNinthOddMarkingLabel k).1.val else 0) ||| m) 0

private theorem original_marker_mask_bit (i : Fin 24) (d : Fin 2048)
    (xs : List (Fin 128)) :
    ((xs.foldr (fun k m =>
      (if (generatedNinthOddMarkingLabel k).2 = i then
        2 ^ (generatedNinthOddMarkingLabel k).1.val else 0) ||| m) 0).testBit d.val = true) ↔
      ∃ k ∈ xs, generatedNinthOddMarkingLabel k = (d, i) := by
  induction xs with
  | nil => simp
  | cons k xs ih =>
    simp only [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true, ih]
    by_cases hk : (generatedNinthOddMarkingLabel k).2 = i
    · simp [hk, Nat.testBit_two_pow, Fin.val_inj, Prod.ext_iff, eq_comm]
    · simp [hk, Prod.ext_iff]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Bind only the24 actual columns of the displayed finite source labels.
/-- Every compact column equals the literal bit union of its displayed preferred source labels. -/
theorem generatedNinth_odd_marking_mask_actual (i : Fin 24) :
    generatedNinthOddMarkingMask i = generatedNinthOddMarkerMaskFold i := by
  revert i
  decide +kernel

/-- A compact marker bit is exactly membership in the displayed genuine preferred odd labels. -/
theorem generatedNinth_odd_marking_mask_mem (d : Fin 2048) (i : Fin 24) :
    (generatedNinthOddMarkingMask i).testBit d.val = true ↔
      (d, i) ∈ generatedNinthOddMarkings := by
  rw [generatedNinth_odd_marking_mask_actual]
  unfold generatedNinthOddMarkerMaskFold
  rw [original_marker_mask_bit]
  simp [generatedNinthOddMarkings]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Check injectivity on the128 displayed dictionary labels.
/-- The displayed preferred odd labels have no repetitions. -/
theorem generatedNinth_odd_marking_labels_injective :
    Function.Injective generatedNinthOddMarkingLabel := by
  decide +kernel

/-- There are128 distinct genuine preferred odd dictionary labels in the displayed marker set. -/
theorem generatedNinth_odd_markings_card : generatedNinthOddMarkings.card = 128 := by
  rw [generatedNinthOddMarkings, Finset.card_image_of_injective _
    generatedNinth_odd_marking_labels_injective, Finset.card_univ]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
