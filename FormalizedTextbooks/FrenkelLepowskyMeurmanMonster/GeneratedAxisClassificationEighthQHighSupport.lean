/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQHighPeriods
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthTensorHighCoverage

/-! The literal high addresses are exactly the original tensor coordinates above the small bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000 in
-- Check both original decoded spin addresses for each of the twelve actual odd labels.
/-- The literal addresses are the actual low and high members of each original omega pair. -/
theorem generatedEighth_high_spin_index_certificate : ∀ j : Fin 12,
    generatedEighthHighSpinIndex (Fin.castAdd 12 j) =
      golayLabelCoefficients ⟨(generatedEighthHighOddCode j).val, by omega⟩ ∧
    generatedEighthHighSpinIndex (Fin.natAdd 12 j) =
      golayLabelCoefficients ⟨(generatedEighthHighOddCode j).val + 2048, by omega⟩ := by
  decide +kernel

/-- Literal high-set membership is exactly belonging to one of the twelve actual odd codes. -/
theorem generatedEighth_high_spin_mem_iff (t : SpinIndex) :
    t ∈ generatedEighthHighSpinSet ↔
      ∃ j : Fin 12, spinDictionaryCode t = generatedEighthHighOddCode j := by
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (m := 12) (n := 12)
      (motive := fun i => ∃ j : Fin 12,
        spinDictionaryCode (generatedEighthHighSpinIndex i) = generatedEighthHighOddCode j)
      (fun j => ?_) (fun j => ?_) i
    · refine ⟨j, ?_⟩
      rw [(generatedEighth_high_spin_index_certificate j).1]
      exact spinDictionaryCode_low _
    · refine ⟨j, ?_⟩
      rw [(generatedEighth_high_spin_index_certificate j).2]
      exact spinDictionaryCode_high _
  · rintro ⟨j, hj⟩
    rcases spinDictionaryIndex_cases t with h | h
    · refine ⟨Fin.castAdd 12 j, ?_⟩
      rw [(generatedEighth_high_spin_index_certificate j).1]
      exact (h.trans (congrArg golayLabelCoefficients (Fin.ext
        (congrArg (fun x : Fin 2048 => x.val) hj)))).symm
    · refine ⟨Fin.natAdd 12 j, ?_⟩
      rw [(generatedEighth_high_spin_index_certificate j).2]
      exact (h.trans (congrArg golayLabelCoefficients (Fin.ext
        (congrArg (fun x : Fin 2048 => x.val + 2048) hj)))).symm

/-- The twenty-four genuine high addresses are exactly those above the proved small square bound. -/
theorem generatedEighth_tensor_high_support (t : SpinIndex) :
    100 < (generatedEighthTensorColumn t) ^ 2 ↔ t ∈ generatedEighthHighSpinSet := by
  constructor
  · intro ht
    by_contra hm
    have hc : ∀ j : Fin 12, spinDictionaryCode t ≠ generatedEighthHighOddCode j := by
      intro j hj
      exact hm ((generatedEighth_high_spin_mem_iff t).mpr ⟨j, hj⟩)
    have hb := generatedEighth_tensor_column_small t hc
    linarith
  · intro ht
    obtain ⟨j, hj⟩ := (generatedEighth_high_spin_mem_iff t).mp ht
    rcases generatedEighth_tensor_high_pair_squares j t hj with h | h
    · rw [h.1]
      norm_num
    · rw [h.1]
      norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
