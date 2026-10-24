/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BernoulliSumPmf
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Tests for the pmf of a sum of independent Bernoulli variables

Generic restatements of the public signatures in
`MathlibExt.Probability.BernoulliSumPmf`, the constant-variable
Bernoulli instances under a Dirac measure, the one-coin and two-coin
fair-coin instances, the vanishing of the pmf above the number of
summands, and the fact that the pmf sums to `1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExtTest.Probability.BernoulliSumPmf

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The general pmf formula restates with the exact public signature. -/
example {m : ℕ} {X : Fin m → Ω → ℕ} {p : Fin m → ℝ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ (p i))
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i))
    (j : ℕ) :
    (μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j})).toReal =
      ∑ A ∈ Finset.univ.powersetCard j,
        (∏ i ∈ A, p i) * (∏ i ∈ Finset.univ \ A, (1 - p i)) :=
  bernoulli_sum_pmf hBernoulli hIndep hMeas j

/-- The i.i.d. binomial pmf restates with the exact public signature. -/
example {m : ℕ} {X : Fin m → Ω → ℕ} {p : ℝ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ p)
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i))
    (j : ℕ) :
    (μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j})).toReal =
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) :=
  bernoulli_sum_pmf_iid hBernoulli hIndep hMeas j

/-- The constant `1` variable is Bernoulli with parameter `1` under any Dirac measure. -/
example {α : Type*} [MeasurableSpace α] (a : α) :
    IsBernoulliRV (fun _ : α => 1) (Measure.dirac a) 1 := by
  refine ⟨zero_le_one, le_refl _, ?_, ?_⟩
  · simp [Measure.dirac]
  · simp [Measure.dirac]

/-- The constant `0` variable is Bernoulli with parameter `0` under any Dirac measure. -/
example {α : Type*} [MeasurableSpace α] (a : α) :
    IsBernoulliRV (fun _ : α => 0) (Measure.dirac a) 0 := by
  refine ⟨le_refl _, zero_le_one, ?_, ?_⟩
  · simp [Measure.dirac]
  · simp [Measure.dirac]

/-- One fair coin: `P(S = 0) = 1 / 2`. -/
example {X : Fin 1 → Ω → ℕ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ (1 / 2))
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i)) :
    (μ ((fun ω => ∑ i : Fin 1, X i ω) ⁻¹' {↑0})).toReal = 1 / 2 := by
  rw [bernoulli_sum_pmf_iid hBernoulli hIndep hMeas 0]
  norm_num

/-- One fair coin: `P(S = 1) = 1 / 2`. -/
example {X : Fin 1 → Ω → ℕ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ (1 / 2))
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i)) :
    (μ ((fun ω => ∑ i : Fin 1, X i ω) ⁻¹' {↑1})).toReal = 1 / 2 := by
  rw [bernoulli_sum_pmf_iid hBernoulli hIndep hMeas 1]
  norm_num

/-- Two fair coins: `P(S = 1) = 1 / 2`. -/
example {X : Fin 2 → Ω → ℕ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ (1 / 2))
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i)) :
    (μ ((fun ω => ∑ i : Fin 2, X i ω) ⁻¹' {↑1})).toReal = 1 / 2 := by
  rw [bernoulli_sum_pmf_iid hBernoulli hIndep hMeas 1]
  norm_num

/-- The pmf vanishes above the number of summands: `P(S = m + 1) = 0`. -/
example {m : ℕ} {X : Fin m → Ω → ℕ} {p : ℝ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ p)
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i)) :
    (μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑(m + 1)})).toReal = 0 := by
  rw [bernoulli_sum_pmf_iid hBernoulli hIndep hMeas (m + 1)]
  simp only [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self m), Nat.cast_zero, zero_mul]

/-- The pmf sums to `1`: `∑_{j=0}^{m} P(S = j) = 1`. -/
theorem bernoulli_sum_pmf_sum_eq_one {m : ℕ} {X : Fin m → Ω → ℕ} {p : ℝ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ p)
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i)) :
    ∑ j ∈ Finset.range (m + 1),
      (μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j})).toReal = 1 := by
  calc ∑ j ∈ Finset.range (m + 1),
        (μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j})).toReal
      = ∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) :=
        Finset.sum_congr rfl (fun j _ => bernoulli_sum_pmf_iid hBernoulli hIndep hMeas j)
    _ = (p + (1 - p)) ^ m := by
        rw [add_pow]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = 1 := by rw [show p + (1 - p) = 1 from by ring, one_pow]

end MathlibExtTest.Probability.BernoulliSumPmf
