/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ChannelCodingAchievability
public import MathlibExtTest.InformationTheory.GallagerExponent

@[expose] public section

/-!
# Tests for Shannon's achievability via Gallager's bound

The noiseless binary channel has capacity at least one bit (the uniform input gives `I = 1`), so
the rate `1/2` is achievable: the hypotheses of `channelCoding_achievability` hold at a positive
rate (non-vacuity). The capacity supremum is bounded above, since `I ≤ H(X) + H(Y)` and every
entropy on `Bool` is at most `2 / ln 2`.
-/

open MeasureTheory Real InformationTheory MathlibExt.InformationTheory.GallagerExponent
  MathlibExt.InformationTheory.ChannelCodingAchievability
  MathlibExtTest.InformationTheory.GallagerExponent

namespace MathlibExtTest.InformationTheory.ChannelCodingAchievability

theorem shannonEntropy_bool_le (q : PMF Bool) : shannonEntropy q ≤ 2 / Real.log 2 := by
  unfold shannonEntropy
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply div_le_div_of_nonneg_right _ hlog.le
  rw [Fintype.sum_bool]
  have h1 := Real.negMulLog_le_one_sub_self (x := (q true).toReal) ENNReal.toReal_nonneg
  have h2 := Real.negMulLog_le_one_sub_self (x := (q false).toReal) ENNReal.toReal_nonneg
  have : 0 ≤ (q true).toReal := ENNReal.toReal_nonneg
  have : 0 ≤ (q false).toReal := ENNReal.toReal_nonneg
  linarith

theorem bddAbove_capacity :
    BddAbove (Set.range fun p : PMF Bool =>
      finiteMutualInformation (p.bind fun a => (noiseless a).map (Prod.mk a))) := by
  refine ⟨4 / Real.log 2, ?_⟩
  rintro _ ⟨p, rfl⟩
  set J := p.bind fun a => (noiseless a).map (Prod.mk a)
  show finiteMutualInformation J ≤ _
  rw [finiteMutualInformation_eq]
  have h1 := shannonEntropy_bool_le (J.map Prod.fst)
  have h2 := shannonEntropy_bool_le (J.map Prod.snd)
  have h3 := shannonEntropy_nonneg J
  have : 2 / Real.log 2 + 2 / Real.log 2 = 4 / Real.log 2 := by ring
  linarith

/-- The uniform input carries one bit through the noiseless binary channel. -/
theorem mutualInformation_unif_noiseless :
    finiteMutualInformation (unif.bind fun a => (noiseless a).map (Prod.mk a)) = 1 := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h := (hasDerivAt_gallagerE0_zero unif noiseless).unique (by
    have h : HasDerivAt (fun ρ : ℝ => ρ * Real.log 2) (Real.log 2) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (Real.log 2)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num)] with ρ hρ
    exact gallagerE0_noiseless hρ)
  have := mul_right_cancel₀ hlog (h.trans (one_mul _).symm)
  exact this

/-- Rate `1/2` bit per use is achievable on the noiseless binary channel, with maximal error at
most `1/10` for all large blocklengths. -/
example : ∀ᶠ n in Filter.atTop, ∃ (M : ℕ) (f : Fin M → Fin n → Bool) (g : (Fin n → Bool) → Fin M),
    (2 : ℝ) ^ ((n : ℝ) * (1 / 2)) ≤ M ∧
      ∀ m, (Measure.pi fun i => (noiseless (f m i)).toMeasure).real {y | g y ≠ m} ≤ 1 / 10 := by
  refine channelCoding_achievability noiseless ?_ (by norm_num)
  refine lt_of_lt_of_le ?_ (le_ciSup bddAbove_capacity unif)
  rw [mutualInformation_unif_noiseless]
  norm_num

end MathlibExtTest.InformationTheory.ChannelCodingAchievability
