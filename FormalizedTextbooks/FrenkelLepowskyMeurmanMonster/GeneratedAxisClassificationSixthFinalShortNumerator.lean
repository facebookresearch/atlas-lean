/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalPairCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalOddCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalOctadCoordinates

/-! The full original short vector has one exact preferred signed integer numerator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Thirty-two times every genuine preferred-short coefficient of the actual sixth axis. -/
def generatedSixthFinalShortNumerator : GriessShortIndex → ℤ
  | Sum.inl (s, p) => generatedSixthFinalPairNumerator s p
  | Sum.inr (Sum.inl (o, e)) => generatedSixthFinalOctadNumerator (golayOctadLabel o) e
  | Sum.inr (Sum.inr (d, j)) => generatedSixthFinalOddNumerator d j

/-- Every original short coordinate equals its complete signed integer numerator over 32. -/
theorem generatedSixth_final_short_numerator (r : GriessShortIndex) :
    (griessConwayEncode generatedSixthAxis).2.1 r =
      (generatedSixthFinalShortNumerator r : ℝ) / 32 := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩)
  · exact generatedSixth_final_pair_coordinate s p
  · exact generatedSixth_final_octad_coordinate o e
  · exact generatedSixth_final_odd_coordinate d j

/-- Signed integer equality gives the genuine original preferred-short coefficient equality. -/
theorem generatedSixth_final_short_signed (r s : GriessShortIndex) (p : ZMod 2)
    (h : nortonUIntegerSign p * generatedSixthFinalShortNumerator r =
      generatedSixthFinalShortNumerator s) :
    qSign p * (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1 s := by
  rw [generatedSixth_final_short_numerator, generatedSixth_final_short_numerator]
  have hh := congrArg (fun z : ℤ => (z : ℝ)) h
  simp only [Int.cast_mul, nortonUIntegerSign_real] at hh
  rw [← mul_div_assoc, hh]

/-- Complete preferred integer transport certifies fixation of the whole short constituent. -/
theorem generatedSixth_short_fixed_of_integer_certificate (f : localFiberSubgroup)
    (h : ∀ r : GriessShortIndex,
      nortonUIntegerSign (localShortPhase f r) * generatedSixthFinalShortNumerator r =
        generatedSixthFinalShortNumerator (griessShortPermutation f.val.2 r)) :
    localShortOperator f (griessConwayEncode generatedSixthAxis).2.1 =
      (griessConwayEncode generatedSixthAxis).2.1 := by
  funext s
  obtain ⟨r, rfl⟩ := (griessShortPermutation f.val.2).surjective s
  rw [localShortOperator_image]
  exact generatedSixth_final_short_signed _ _ _ (h r)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
