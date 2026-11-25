/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.BetaBinomialSampleRank
public import MathlibExt.MeasureTheory.Measure.Atomless

@[expose] public section

open MeasureTheory ProbabilityTheory Polynomial Finset
  MathlibExt.Probability.Statistics.SplitConformal
  MathlibExt.Probability.Distributions.BetaBinomialSampleRank

namespace MathlibExtTest.Probability.Distributions.BetaBinomialSampleRank

/-- The uniform law on `[0, 1]`, an atomless probability measure, for non-vacuity checks. -/
noncomputable abbrev unifIcc : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unifIcc := ⟨by simp [unifIcc]⟩

/-- Non-vacuity: the law of `K` for `m + 1 = 3` real and `N = 4` synthetic i.i.d. uniform scores
and the median real score `r = 2`. -/
example {k : ℕ} (hk : 1 ≤ k) :
    (Measure.pi fun _ : Fin (2 + 1) ⊕ Fin 4 => unifIcc).real {ω | sampleRank 2 ω + 1 = k} =
      betaBinomialPMF 4 2 ((2 : ℕ) + 2 - (2 : ℕ) : ℝ) (k - 1) :=
  measureReal_sampleRank_add_one_eq (by norm_num) (by norm_num) unifIcc hk

/-- Boundary `r = m + 1` (the largest real score) is allowed. -/
example (m N : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (Measure.pi fun _ : Fin (m + 1) ⊕ Fin N => unifIcc).real
        {ω | sampleRank (m + 1) ω + 1 = k} =
      betaBinomialPMF N (m + 1 : ℕ) ((m : ℝ) + 2 - (m + 1 : ℕ)) (k - 1) :=
  measureReal_sampleRank_add_one_eq (by omega) le_rfl unifIcc hk

/-- `N = 0`: there are no synthetic scores, so `J = 0`, i.e. `K = 1`, and `BB(0; α, β)(0) = 1`. -/
example (m r : ℕ) (ω : Fin (m + 1) ⊕ Fin 0 → ℝ) : sampleRank r ω = 0 := by
  simp [sampleRank]

example (α β : ℝ) : betaBinomialPMF 0 α β 0 = 1 := by
  simp [betaBinomialPMF]

/-- `m = 0`, `r = 1`: one real score, whose rank among `N = 3` synthetic scores is uniform. -/
example (j : ℕ) (hj : j ≤ 3) : betaBinomialPMF 3 1 ((0 : ℕ) + 2 - (1 : ℕ) : ℝ) j = 1 / 4 := by
  interval_cases j <;> norm_num [betaBinomialPMF, ascPochhammer_succ_eval, Nat.choose]

/-- The binomial-ratio form agrees with the beta-binomial mass, e.g. `m = 2`, `N = 4`, `r = 2`,
`j = 1`: `C(2, 1) C(4, 1) / C(7, 3) = 8 / 35`. -/
example : betaBinomialPMF 4 ((2 : ℕ) : ℝ) ((2 : ℕ) + 2 - (2 : ℕ) : ℝ) 1 = 8 / 35 := by
  rw [← choose_mul_choose_div_choose_eq_betaBinomialPMF (m := 2) (by norm_num) (by norm_num)
    (by norm_num)]
  norm_num [Nat.choose]

/-- The accepted example `m = 1`, `N = 5`, `r = 1`: `P(K = k) = (7 - k) / 21`. -/
example (k : ℕ) (hk : 1 ≤ k) (hk6 : k ≤ 6) :
    betaBinomialPMF 5 1 ((1 : ℕ) + 2 - (1 : ℕ) : ℝ) (k - 1) = (7 - k) / 21 := by
  interval_cases k <;> norm_num [betaBinomialPMF, ascPochhammer_succ_eval, Nat.choose]

/-- The accepted example `m = 1`, `N = 5`, `r = 1`: the window `[S̃₍₁₎, S̃₍₅₎]` covers the
smaller real score with probability `F 5 - F 1 = 2 / 3`. -/
example :
    (Measure.pi fun _ : Fin (1 + 1) ⊕ Fin 5 => unifIcc).real
        {ω | (1 = 0 ∨ syntheticOrderStatistic 1 ω ≤ realOrderStatistic 1 ω) ∧
          realOrderStatistic 1 ω ≤ syntheticOrderStatistic 5 ω} = 2 / 3 := by
  rw [measureReal_window (by norm_num) (by norm_num) (by norm_num) unifIcc,
    measureReal_sampleRank_add_one_le (by norm_num) (by norm_num) unifIcc,
    measureReal_sampleRank_add_one_le (by norm_num) (by norm_num) unifIcc]
  norm_num [Finset.sum_range_succ, betaBinomialPMF, ascPochhammer_succ_eval, Nat.choose]

/-- Mean for the accepted example: `E K = 1 + 5 · 1 / 3 = 8 / 3`. -/
example :
    ∫ ω, ((sampleRank 1 ω : ℝ) + 1) ∂(Measure.pi fun _ : Fin (1 + 1) ⊕ Fin 5 => unifIcc) =
      8 / 3 := by
  rw [integral_sampleRank_add_one (by norm_num) (by norm_num) unifIcc]
  norm_num

/-- Ties break the window event identity: with all scores equal to `0` (`m = 0`, `N = 1`,
`r = 1`), `S̃₍₁₎ ≤ S₍₁₎ ≤ S̃₍₂₎ = ⊤` holds but `J = 0 < 1`. This is why `window_iff_of_injective`
assumes distinct scores and `measureReal_window` is an almost-sure statement. -/
example :
    ((1 = 0 ∨ syntheticOrderStatistic 1 (fun _ : Fin (0 + 1) ⊕ Fin 1 => (0 : ℝ)) ≤
        realOrderStatistic 1 (fun _ : Fin (0 + 1) ⊕ Fin 1 => (0 : ℝ))) ∧
      realOrderStatistic 1 (fun _ : Fin (0 + 1) ⊕ Fin 1 => (0 : ℝ)) ≤
        syntheticOrderStatistic 2 (fun _ : Fin (0 + 1) ⊕ Fin 1 => (0 : ℝ))) ∧
      ¬ 1 ≤ sampleRank 1 (fun _ : Fin (0 + 1) ⊕ Fin 1 => (0 : ℝ)) := by
  have h1 : realOrderStatistic 1 (fun _ : Fin (0 + 1) ⊕ Fin 1 => (0 : ℝ)) = ((0 : ℝ) : WithTop ℝ) :=
    (orderStatistic_eq_coe_iff le_rfl 0).2 (by simp)
  have h2 : syntheticOrderStatistic 1 (fun _ : Fin (0 + 1) ⊕ Fin 1 => (0 : ℝ)) =
      ((0 : ℝ) : WithTop ℝ) :=
    (orderStatistic_eq_coe_iff le_rfl 0).2 (by simp)
  have h3 := syntheticOrderStatistic_succ_eq_top (m := 0) (N := 1) fun _ => (0 : ℝ)
  refine ⟨⟨Or.inr (by rw [h1, h2]), by rw [h3]; exact le_top⟩, ?_⟩
  simp [sampleRank, h1]

/-- Atomless laws in the sense of `IsAtomless` have null singletons, so the theorems apply. -/
example (ν : Measure ℝ) (h : IsAtomless ν) : NullSingletonClass ν :=
  h.nullSingletonClass

end MathlibExtTest.Probability.Distributions.BetaBinomialSampleRank

#print axioms measureReal_sampleRank_eq_of_exchangeable
#print axioms measureReal_sampleRank_add_one_eq
#print axioms measureReal_sampleRank_add_one_eq_choose
#print axioms integral_sampleRank_add_one
#print axioms measureReal_window
open MathlibExt.Probability.Statistics.MultipleTesting in
#print axioms measure_eq_card_div_of_ae_card_filter_smul_mem_eq
