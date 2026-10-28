/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCountCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCountTotals

/-! Exact enumeration of the actual norm-eight integral Leech vectors.
Source residues have a unique parity/code-word parameter, and the generating
series counts every bounded coordinate assignment. Certified convolution and
summing the actual Golay encoding give the complete vector count. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The norm-eight source fiber depends on the actual codeword weight. -/
theorem leechNormEightBoundedSolution_card (m : Bool) (c : golayCode) :
    Nat.card (LeechNormEightBoundedSolution m c) =
      leechNormEightWordContribution m (∑ i, (c.val i).val) := by
  have hw := golayCode_weights c.val c.property
  have hk : ∃ k : Fin 5,
      (leechNormEightGolayWeights k).val = ∑ i, (c.val i).val := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩
    · exact ⟨4, h.symm⟩
  obtain ⟨k, hk⟩ := hk
  rw [← leechNormEightWordSeries_count, leechNormEightWordSeries_weight, ← hk,
    leechNormEightSeries_product]
  calc
    _ = ∑ q : Fin 65, ∑ r : ZMod 8,
        leechNormEightCountTable m 0
          ⟨24 - (leechNormEightGolayWeights k).val, by omega⟩ q r *
        leechNormEightCountTable m 1 (leechNormEightGolayWeights k)
          ⟨64 - q.val, by omega⟩ (4 * (m.toNat : ZMod 8) - r) := by
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      rw [leechNormEightCountTable_sound m 0 _ (by omega) _ q.isLt,
        leechNormEightCountTable_sound m 1 _ (leechNormEightGolayWeights k).isLt _ (by omega)]
    _ = _ := leechNormEightCountTable_product m k

/-- Exactly 398034000 actual integral Leech vectors have squared physical norm eight. -/
theorem leechNormEight_card : Nat.card LeechNormEight = 398034000 := by
  let _ := Fintype.ofFinite golayCode
  rw [← Nat.card_congr leechNormEightSourceEquiv]
  change Nat.card (Σ m : Bool, Σ c : golayCode, LeechNormEightBoundedSolution m c) = _
  rw [Nat.card_sigma]
  simp_rw [Nat.card_sigma, leechNormEightBoundedSolution_card]
  rw [Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  rw [← Equiv.sum_comp golayCodeLabelEquiv]
  simp only [leechNormEightWordContribution, Bool.false_eq_true, ite_true, ite_false,
    golayCodeLabelEquiv_val]
  simp_rw [← golayLabel_weight]
  calc
    _ = ∑ d : Fin 4096,
        (leechNormEightEvenContribution (golayMaskWeight (golayEncodedMask d.val)) + 48576) := by
      apply Finset.sum_congr rfl
      intro d _
      exact Nat.add_comm _ _
    _ = 398034000 := leechNormEightContribution_sum

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
