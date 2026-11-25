/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.HighDimensionalStatistics

/-! # Tests for `MathlibExt.Probability.HighDimensionalStatistics` -/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace MathlibExtTest.Probability.HighDimensionalStatistics

open MathlibExt.Probability.HighDimensionalStatisticsWanted

/-! ### Bernstein's condition -/

/-- The fair coin on `Bool`. -/
noncomputable def coin : Measure Bool := (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure coin :=
  ⟨by
    simp only [coin, smul_apply, add_apply, measure_univ, smul_eq_mul, ← two_mul,
      mul_one]
    exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top⟩

lemma integral_coin (f : Bool → ℝ) : ∫ b, f b ∂coin = (f true + f false) / 2 := by
  rw [coin, integral_smul_measure, integral_add_measure .of_finite .of_finite, integral_dirac,
    integral_dirac]
  simp [ENNReal.toReal_inv]
  ring

/-- A Rademacher variable: `±1` with probability `1/2` each. -/
def rademacher (b : Bool) : ℝ := if b then 1 else -1

lemma integral_rademacher_pow (k : ℕ) :
    ∫ b, rademacher b ^ k ∂coin = (1 + (-1) ^ k) / 2 := by
  simp [integral_coin, rademacher]

/-- A Rademacher variable satisfies the Bernstein condition with `σ = 1` and `b = 1`:
`|E[X^k]| ≤ 1 ≤ k! / 2` for `k ≥ 3`. -/
lemma rademacher_bernstein (k : ℕ) (hk : 3 ≤ k) :
    |∫ b, rademacher b ^ k ∂coin| ≤ k.factorial * (1 : ℝ) ^ 2 * 1 ^ (k - 2) / 2 := by
  rw [integral_rademacher_pow]
  have hfac : (6 : ℝ) ≤ k.factorial := by
    have : (3 : ℕ).factorial ≤ k.factorial := Nat.factorial_le hk
    exact_mod_cast this
  have habs : |(1 + (-1 : ℝ) ^ k) / 2| ≤ 1 := by
    rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h] <;> norm_num
  simp only [one_pow, mul_one]
  linarith

-- Test section: Bernstein's moment generating function bound for a Rademacher variable at
-- `t = 1/2`: `E[exp (X / 2)] = cosh (1/2) ≤ exp (1/4)`.
example : mgf rademacher coin (1 / 2) ≤ exp (1 / 4) := by
  have h := (mgf_le_of_bernsteinCondition (μ := coin) (X := rademacher) (b := 1) (σ := 1)
    zero_le_one (fun _ ↦ .of_finite) (by simpa using integral_rademacher_pow 1)
    (by simpa using integral_rademacher_pow 2) rademacher_bernstein
    (t := 1 / 2) (by norm_num)).2
  norm_num at h
  exact h

-- Bernstein's inequality for the same variable at `t = 1`: `P(|X| ≥ 1) = 1 ≤ 2 exp (-1/4)`.
example : coin.real {b | 1 ≤ |rademacher b|} ≤ 2 * exp (-1 / 4) := by
  have h := measureReal_abs_ge_le_of_bernsteinCondition (μ := coin) (X := rademacher) (b := 1)
    (σ := 1) zero_le_one (fun _ ↦ .of_finite) (by simpa using integral_rademacher_pow 1)
    (by simpa using integral_rademacher_pow 2) rademacher_bernstein (t := 1) zero_le_one
  norm_num at h ⊢
  exact h

-- Edge case `b = 0`: the condition then forces `X = 0` almost surely; the zero variable, with
-- `σ = 0`, satisfies it, and the bound holds at every `t`.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] (t : ℝ) :
    Integrable (fun ω ↦ exp (t * (fun _ : Ω ↦ (0 : ℝ)) ω)) μ ∧
      mgf (fun _ : Ω ↦ (0 : ℝ)) μ t ≤ exp (t ^ 2 * 0 ^ 2 / (2 * (1 - 0 * |t|))) :=
  mgf_le_of_bernsteinCondition le_rfl (fun _ ↦ integrable_const _) (by simp) (by simp)
    (fun k hk ↦ by rw [zero_pow (by omega)]; simp) (by simp)

-- Edge case `σ = 0` with `b > 0`: Bernstein's inequality for the zero variable at `t = 1`.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] :
    μ.real {ω | 1 ≤ |(fun _ : Ω ↦ (0 : ℝ)) ω|} ≤
      2 * exp (-1 ^ 2 / (2 * ((0 : ℝ) ^ 2 + 1 * 1))) :=
  measureReal_abs_ge_le_of_bernsteinCondition zero_le_one (fun _ ↦ integrable_const _) (by simp)
    (by simp) (fun k hk ↦ by rw [zero_pow (by omega)]; simp) zero_le_one

/-! ### The `χ²` distribution -/

-- Test section: the centred `χ²₁` variable. Its moment generating function at `t = 1/8` is at
-- most `exp (4 (1/8)² / 2) = exp (1/32)`.
example : mgf (fun x : ℝ ↦ x ^ 2 - 1) (gaussianReal 0 1) (1 / 8) ≤ exp (1 / 32) := by
  have h := hasSubexponentialMGF_sq_sub_one_gaussianReal.mgf_le (1 / 8) (by norm_num)
  norm_num at h
  exact h

-- The sub-exponential tail bounds then apply to `Z² - 1`, in the Gaussian regime at `t = 1`
-- (`P(Z² ≥ 2) ≤ exp (-1/8)`) and in the exponential regime at `t = 2` (`P(Z² ≥ 3) ≤ exp (-1/4)`).
example : (gaussianReal 0 1).real {x | 1 ≤ x ^ 2 - 1} ≤ exp (-1 / 8) := by
  have h := hasSubexponentialMGF_sq_sub_one_gaussianReal.measureReal_ge_le_of_le zero_le_one
    (by norm_num)
  norm_num at h ⊢
  exact h

example : (gaussianReal 0 1).real {x | 2 ≤ x ^ 2 - 1} ≤ exp (-1 / 4) := by
  have h := hasSubexponentialMGF_sq_sub_one_gaussianReal.measureReal_ge_le_of_ge (by norm_num)
    (t := 2) (by norm_num)
  norm_num at h ⊢
  exact h

-- Test section: the `χ²_n` tail bound. For `n = 1` and `t = 1/2`:
-- `P(|Z² - 1| ≥ 1/2) ≤ 2 exp (-1/32)`.
example : (Measure.pi fun _ : Fin 1 ↦ gaussianReal 0 1).real
    {z | 1 / 2 ≤ |(1 / ((1 : ℕ) : ℝ)) * ∑ k, z k ^ 2 - 1|} ≤ 2 * exp (-1 / 32) := by
  have h := measureReal_abs_chiSq_mean_sub_one_ge_le 1 (t := 1 / 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

-- For `n = 100` and `t = 1/2`, the bound is `2 exp (-25/8)`, below `0.1`.
example : (Measure.pi fun _ : Fin 100 ↦ gaussianReal 0 1).real
    {z | 1 / 2 ≤ |(1 / ((100 : ℕ) : ℝ)) * ∑ k, z k ^ 2 - 1|} ≤ 2 * exp (-25 / 8) := by
  have h := measureReal_abs_chiSq_mean_sub_one_ge_le 100 (t := 1 / 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

-- Edge case `n = 0`: the empirical mean is `1 / 0 * 0 = 0`, so the event is the whole space and
-- has probability `1`, within the bound `2 exp 0 = 2`.
example {t : ℝ} (ht1 : t < 1) : (Measure.pi fun _ : Fin 0 ↦ gaussianReal 0 1).real
    {z | t ≤ |(1 / ((0 : ℕ) : ℝ)) * ∑ k, z k ^ 2 - 1|} = 1 := by
  have : {z : Fin 0 → ℝ | t ≤ |(1 / ((0 : ℕ) : ℝ)) * ∑ k, z k ^ 2 - 1|} = Set.univ := by
    ext z
    simp only [Nat.cast_zero, div_zero, zero_mul, zero_sub, abs_neg, abs_one,
      Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ht1.le
  rw [this, probReal_univ]

end MathlibExtTest.Probability.HighDimensionalStatistics
