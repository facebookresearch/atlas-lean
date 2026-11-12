/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.ExpectedShortfall
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Value-at-risk is not subadditive

Two independent losses of 100 with probability 0.04 each have `VaR_0.95 = 0`
individually but `VaR_0.95 = 100` for the sum, so value-at-risk is not subadditive:
`VaR(X₁ + X₂) = 100 > 0 = VaR(X₁) + VaR(X₂)`. Value-at-risk is the lower
`0.95`-quantile (`cdfQuantile`) of the loss law; the single loss has
`P(L ≤ 0) = 0.96 ≥ 0.95`, while the sum has `P(sum ≤ 0) = 0.9216 < 0.95 ≤
P(sum ≤ 100) = 0.9984`.

## Main results

* `valueAtRisk`: the lower-quantile value-at-risk of a loss law.
* `prodWeights`, `loss1`, `loss2`: the two independent losses.
* `cdf_loss_single_eq`, `cdf_loss2_eq`, `cdf_loss_sum_eq`: the exact cdfs.
* `valueAtRisk_loss_single_eq_zero`, `valueAtRisk_loss2_eq_zero`,
  `valueAtRisk_loss_sum_eq`: the three VaR values.
* `valueAtRisk_not_subadditive`: the failure of subadditivity.

## References

* P. Artzner, F. Delbaen, J.-M. Eber, D. Heath, *Coherent measures of risk*,
  Math. Finance 9 (1999), 203–228 (VaR is not coherent; subadditivity fails).
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.ValueAtRisk

open MeasureTheory ProbabilityTheory
open Set
open MathlibExt.Probability.Finance.ExpectedShortfall

/-- Value-at-risk at level `α`: the lower `α`-quantile of the loss law (source clause:
"VaR is the quantile of the loss distribution"). -/
noncomputable def valueAtRisk (μ : Measure ℝ) (α : ℝ) : ℝ :=
  ProbabilityTheory.cdfQuantile μ α

/-- The product weights of two independent losses: each loss is 100 with probability 0.04
and 0 with probability 0.96, independently (source clause: "two independent losses of 100
with probability 0.04 each"). `ω.1` is the first loss's Bernoulli outcome (`1` = loss),
`ω.2` the second's. -/
noncomputable def prodWeights : Fin 2 × Fin 2 → ℝ :=
  fun ω => (if ω.1 = 1 then (0.04 : ℝ) else 0.96) * (if ω.2 = 1 then (0.04 : ℝ) else 0.96)

/-- The first loss: 100 when the first outcome is a loss, else 0. -/
noncomputable def loss1 : Fin 2 × Fin 2 → ℝ :=
  fun ω => if ω.1 = 1 then 100 else 0

/-- The second loss: 100 when the second outcome is a loss, else 0. -/
noncomputable def loss2 : Fin 2 × Fin 2 → ℝ :=
  fun ω => if ω.2 = 1 then 100 else 0

/-- The product weights are nonnegative. -/
theorem prodWeights_nonneg : ∀ ω : Fin 2 × Fin 2, 0 ≤ prodWeights ω := by
  intro ω
  simp only [prodWeights]
  split_ifs <;> norm_num

/-- The product weights sum to 1. -/
theorem prodWeights_sum_eq_one : ∑ ω : Fin 2 × Fin 2, prodWeights ω = 1 := by
  have h0 : (0 : Fin 2) ≠ 1 := by decide
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, prodWeights, ite_eq_right h0, ite_true]
  norm_num

/-- The cdf of the first loss: `0` below `0`, `0.96` on `[0, 100)`, `1` from `100` on. -/
theorem cdf_loss_single_eq (x : ℝ) :
    cdf (lossLaw prodWeights loss1) x =
      if x < 0 then 0 else if x < 100 then 0.96 else 1 := by
  have h0 : (0 : Fin 2) ≠ 1 := by decide
  rw [cdf_lossLaw_eq prodWeights_nonneg prodWeights_sum_eq_one]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, loss1, prodWeights, ite_eq_right h0, ite_true]
  by_cases hx0 : x < 0
  · have h0x : ¬ (0 : ℝ) ≤ x := by linarith
    have h100x : ¬ (100 : ℝ) ≤ x := by linarith
    simp only [ite_eq_left hx0, ite_eq_right h0x, ite_eq_right h100x]
    norm_num
  · by_cases hx100 : x < 100
    · have h0x : (0 : ℝ) ≤ x := by linarith
      have h100x : ¬ (100 : ℝ) ≤ x := by linarith
      simp only [ite_eq_right hx0, ite_eq_left hx100, ite_eq_left h0x,
        ite_eq_right h100x]
      norm_num
    · have h0x : (0 : ℝ) ≤ x := by linarith
      have h100x : (100 : ℝ) ≤ x := by linarith
      simp only [ite_eq_right hx0, ite_eq_right hx100, ite_eq_left h0x,
        ite_eq_left h100x]
      norm_num

/-- The cdf of the second loss: same as the first (the two losses are identically
distributed). -/
theorem cdf_loss2_eq (x : ℝ) :
    cdf (lossLaw prodWeights loss2) x =
      if x < 0 then 0 else if x < 100 then 0.96 else 1 := by
  have h0 : (0 : Fin 2) ≠ 1 := by decide
  rw [cdf_lossLaw_eq prodWeights_nonneg prodWeights_sum_eq_one]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, loss2, prodWeights, ite_eq_right h0, ite_true]
  by_cases hx0 : x < 0
  · have h0x : ¬ (0 : ℝ) ≤ x := by linarith
    have h100x : ¬ (100 : ℝ) ≤ x := by linarith
    simp only [ite_eq_left hx0, ite_eq_right h0x, ite_eq_right h100x]
    norm_num
  · by_cases hx100 : x < 100
    · have h0x : (0 : ℝ) ≤ x := by linarith
      have h100x : ¬ (100 : ℝ) ≤ x := by linarith
      simp only [ite_eq_right hx0, ite_eq_left hx100, ite_eq_left h0x,
        ite_eq_right h100x]
      norm_num
    · have h0x : (0 : ℝ) ≤ x := by linarith
      have h100x : (100 : ℝ) ≤ x := by linarith
      simp only [ite_eq_right hx0, ite_eq_right hx100, ite_eq_left h0x,
        ite_eq_left h100x]
      norm_num

/-- The cdf of the sum of the two losses: `0` below `0`, `0.9216 = 0.96²` on `[0, 100)`,
`0.9984 = 0.9216 + 2 * 0.96 * 0.04` on `[100, 200)`, `1` from `200` on. The sum takes
values `0`, `100`, `200` with probabilities `0.9216`, `0.0768`, `0.0016`. -/
theorem cdf_loss_sum_eq (x : ℝ) :
    cdf (lossLaw prodWeights (loss1 + loss2)) x =
      if x < 0 then 0 else if x < 100 then 0.9216 else if x < 200 then 0.9984 else 1 := by
  have h0 : (0 : Fin 2) ≠ 1 := by decide
  have e00 : (loss1 + loss2) ((0, 0) : Fin 2 × Fin 2) = 0 := by
    simp only [Pi.add_apply, loss1, loss2, ite_eq_right h0, zero_add]
  have e01 : (loss1 + loss2) ((0, 1) : Fin 2 × Fin 2) = 100 := by
    simp only [Pi.add_apply, loss1, loss2, ite_eq_right h0, ite_true, zero_add]
  have e10 : (loss1 + loss2) ((1, 0) : Fin 2 × Fin 2) = 100 := by
    simp only [Pi.add_apply, loss1, loss2, ite_eq_right h0, ite_true, add_zero]
  have e11 : (loss1 + loss2) ((1, 1) : Fin 2 × Fin 2) = 200 := by
    simp only [Pi.add_apply, loss1, loss2, ite_true]
    norm_num
  rw [cdf_lossLaw_eq prodWeights_nonneg prodWeights_sum_eq_one]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, prodWeights, ite_eq_right h0, ite_true]
  rw [e00, e01, e10, e11]
  by_cases hx0 : x < 0
  · have h0x : ¬ (0 : ℝ) ≤ x := by linarith
    have h100x : ¬ (100 : ℝ) ≤ x := by linarith
    have h200x : ¬ (200 : ℝ) ≤ x := by linarith
    simp only [ite_eq_left hx0, ite_eq_right h0x, ite_eq_right h100x,
      ite_eq_right h200x]
    norm_num
  · by_cases hx100 : x < 100
    · have h0x : (0 : ℝ) ≤ x := by linarith
      have h100x : ¬ (100 : ℝ) ≤ x := by linarith
      have h200x : ¬ (200 : ℝ) ≤ x := by linarith
      simp only [ite_eq_right hx0, ite_eq_left hx100, ite_eq_left h0x,
        ite_eq_right h100x, ite_eq_right h200x]
      norm_num
    · by_cases hx200 : x < 200
      · have h0x : (0 : ℝ) ≤ x := by linarith
        have h100x : (100 : ℝ) ≤ x := by linarith
        have h200x : ¬ (200 : ℝ) ≤ x := by linarith
        simp only [ite_eq_right hx0, ite_eq_right hx100, ite_eq_left hx200,
          ite_eq_left h0x, ite_eq_left h100x, ite_eq_right h200x]
        norm_num
      · have h0x : (0 : ℝ) ≤ x := by linarith
        have h100x : (100 : ℝ) ≤ x := by linarith
        have h200x : (200 : ℝ) ≤ x := by linarith
        simp only [ite_eq_right hx0, ite_eq_right hx100, ite_eq_right hx200,
          ite_eq_left h0x, ite_eq_left h100x, ite_eq_left h200x]
        norm_num

/-- **VaR of one loss is 0.** At level `0.95`, the single loss (100 with probability 0.04)
has `VaR = 0`: the set `{x | 0.95 ≤ cdf x}` is `Ici 0`, whose infimum is `0`.

Proof route (not mandatory): unfold `valueAtRisk` and `cdfQuantile` (the level `95/100`
is in `Ioo 0 1`), show `{x | 95/100 ≤ cdf (lossLaw prodWeights loss1) x} = Ici 0` from
`cdf_loss_single_eq` (for `x < 0` the cdf is `0 < 0.95`; for `x ≥ 0` it is at least
`0.96 ≥ 0.95`), then `csInf_Ici`. -/
theorem valueAtRisk_loss_single_eq_zero :
    valueAtRisk (lossLaw prodWeights loss1) (95 / 100) = 0 := by
  have hmem : (95 : ℝ) / 100 ∈ Ioo (0 : ℝ) 1 := by
    simp only [mem_Ioo]
    constructor <;> norm_num
  unfold valueAtRisk ProbabilityTheory.cdfQuantile
  rw [ite_eq_left hmem]
  have hset : {x : ℝ | (95 : ℝ) / 100 ≤ cdf (lossLaw prodWeights loss1) x}
      = Ici 0 := by
    ext x
    simp only [mem_ofPred_eq, mem_Ici]
    rw [cdf_loss_single_eq]
    by_cases hx0 : x < 0
    · rw [ite_eq_left hx0]
      constructor <;> intro _ <;> linarith
    · rw [ite_eq_right hx0]
      by_cases hx100 : x < 100
      · rw [ite_eq_left hx100]
        constructor
        · intro _; linarith
        · intro _; norm_num
      · rw [ite_eq_right hx100]
        constructor
        · intro _; linarith
        · intro _; norm_num
  rw [hset, csInf_Ici]

/-- **VaR of the second loss is 0**, by the same argument (identical distribution). -/
theorem valueAtRisk_loss2_eq_zero :
    valueAtRisk (lossLaw prodWeights loss2) (95 / 100) = 0 := by
  have hmem : (95 : ℝ) / 100 ∈ Ioo (0 : ℝ) 1 := by
    simp only [mem_Ioo]
    constructor <;> norm_num
  unfold valueAtRisk ProbabilityTheory.cdfQuantile
  rw [ite_eq_left hmem]
  have hset : {x : ℝ | (95 : ℝ) / 100 ≤ cdf (lossLaw prodWeights loss2) x}
      = Ici 0 := by
    ext x
    simp only [mem_ofPred_eq, mem_Ici]
    rw [cdf_loss2_eq]
    by_cases hx0 : x < 0
    · rw [ite_eq_left hx0]
      constructor <;> intro _ <;> linarith
    · rw [ite_eq_right hx0]
      by_cases hx100 : x < 100
      · rw [ite_eq_left hx100]
        constructor
        · intro _; linarith
        · intro _; norm_num
      · rw [ite_eq_right hx100]
        constructor
        · intro _; linarith
        · intro _; norm_num
  rw [hset, csInf_Ici]

/-- **VaR of the sum is 100.** At level `0.95` the sum has `VaR = 100`: the set
`{x | 0.95 ≤ cdf x}` is `Ici 100` (the cdf is `0.9216 < 0.95` below `100` and
`0.9984 ≥ 0.95` from `100` on), whose infimum is `100`. -/
theorem valueAtRisk_loss_sum_eq :
    valueAtRisk (lossLaw prodWeights (loss1 + loss2)) (95 / 100) = 100 := by
  have hmem : (95 : ℝ) / 100 ∈ Ioo (0 : ℝ) 1 := by
    simp only [mem_Ioo]
    constructor <;> norm_num
  unfold valueAtRisk ProbabilityTheory.cdfQuantile
  rw [ite_eq_left hmem]
  have hset : {x : ℝ | (95 : ℝ) / 100 ≤ cdf (lossLaw prodWeights (loss1 + loss2)) x}
      = Ici 100 := by
    ext x
    simp only [mem_ofPred_eq, mem_Ici]
    rw [cdf_loss_sum_eq]
    by_cases hx0 : x < 0
    · rw [ite_eq_left hx0]
      constructor <;> intro _ <;> linarith
    · rw [ite_eq_right hx0]
      by_cases hx100 : x < 100
      · rw [ite_eq_left hx100]
        constructor <;> intro _ <;> linarith
      · rw [ite_eq_right hx100]
        by_cases hx200 : x < 200
        · rw [ite_eq_left hx200]
          constructor
          · intro _; linarith
          · intro _; norm_num
        · rw [ite_eq_right hx200]
          constructor
          · intro _; linarith
          · intro _; norm_num
  rw [hset, csInf_Ici]

/-- **Value-at-risk is not subadditive** (Atlas roadmap FI13.T01): the VaR of the sum
(`100`) strictly exceeds the sum of the individual VaRs (`0 + 0`). -/
theorem valueAtRisk_not_subadditive :
    valueAtRisk (lossLaw prodWeights loss1) (95 / 100) +
        valueAtRisk (lossLaw prodWeights loss2) (95 / 100) <
      valueAtRisk (lossLaw prodWeights (loss1 + loss2)) (95 / 100) := by
  rw [valueAtRisk_loss_single_eq_zero, valueAtRisk_loss2_eq_zero,
    valueAtRisk_loss_sum_eq]
  norm_num

end MathlibExt.Probability.Finance.ValueAtRisk
