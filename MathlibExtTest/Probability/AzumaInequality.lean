/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.AzumaInequality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Tests for `MathlibExt.Probability.AzumaInequality` -/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace MathlibExtTest.AzumaInequality

open MathlibExt.Probability.AzumaInequalityWanted

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {Z : ℕ → Ω → ℝ}

-- Test section: Azuma's inequality. Unit increments and `a = λ √n` give
-- `P(Zₙ - Z₀ ≥ λ √n) ≤ exp (-λ² / 2)`, the special case in the docstring.
example (hZ : Martingale Z ℱ μ) {n : ℕ} (hn : 0 < n)
    (hc : ∀ i ∈ Finset.Icc 1 n, ∀ ω, |Z i ω - Z (i - 1) ω| ≤ 1) {l : ℝ} (hl : 0 < l) :
    μ.real {ω | l * √n ≤ Z n ω - Z 0 ω} ≤ exp (-l ^ 2 / 2) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h := azuma_inequality hZ n (fun _ ↦ 1) hc (a := l * √n) (by positivity)
  have he : -(l * √n) ^ 2 / (2 * ∑ i ∈ Finset.Icc 1 n, (fun _ ↦ (1 : ℝ)) i ^ 2) =
      -l ^ 2 / 2 := by
    simp only [one_pow, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul,
      mul_one]
    rw [mul_pow, sq_sqrt hn'.le]
    field_simp
  rwa [he] at h

-- When every `cᵢ` vanishes, `∑ cᵢ² = 0` and the bound is `exp (-a² / 0) = exp 0 = 1`, by Lean's
-- convention `x / 0 = 0`.
example (n : ℕ) (a : ℝ) :
    exp (-a ^ 2 / (2 * ∑ i ∈ Finset.Icc 1 n, (0 : ℕ → ℝ) i ^ 2)) = 1 := by
  simp

-- A constant martingale has such increments.
example (x : ℝ) (n : ℕ) {a : ℝ} (ha : 0 < a) :
    μ.real {ω | a ≤ (fun _ _ ↦ x : ℕ → Ω → ℝ) n ω - (fun _ _ ↦ x : ℕ → Ω → ℝ) 0 ω} ≤
      exp (-a ^ 2 / (2 * ∑ i ∈ Finset.Icc 1 n, (0 : ℕ → ℝ) i ^ 2)) :=
  azuma_inequality (martingale_const ℱ μ x) n 0 (by simp) ha

-- Applied to `-Z`, Azuma's inequality gives the lower tail.
example (hZ : Martingale Z ℱ μ) (n : ℕ) (c : ℕ → ℝ)
    (hc : ∀ i ∈ Finset.Icc 1 n, ∀ ω, |Z i ω - Z (i - 1) ω| ≤ c i) {a : ℝ} (ha : 0 < a) :
    μ.real {ω | Z n ω - Z 0 ω ≤ -a} ≤ exp (-a ^ 2 / (2 * ∑ i ∈ Finset.Icc 1 n, c i ^ 2)) := by
  have h := azuma_inequality hZ.neg n c (fun i hi ω ↦ by
    rw [Pi.neg_apply, Pi.neg_apply, Pi.neg_apply, Pi.neg_apply, neg_sub_neg, abs_sub_comm]
    exact hc i hi ω) ha
  convert h using 3
  ext ω
  simp only [Pi.neg_apply]
  constructor <;> intro <;> linarith

-- Test section: the martingale bound. Bounds on increments that hold only almost everywhere
-- suffice, and the parameter of `Zₙ - Z₀` is `∑ cᵢ²`.
example (hZ : Martingale Z ℱ μ) (n : ℕ) (c : ℕ → ℝ)
    (hc : ∀ i ∈ Finset.Icc 1 n, ∀ᵐ ω ∂μ, |Z i ω - Z (i - 1) ω| ≤ c i) (t : ℝ) :
    mgf (fun ω ↦ Z n ω - Z 0 ω) μ t ≤ exp ((∑ i ∈ Finset.Icc 1 n, c i ^ 2) * t ^ 2 / 2) := by
  have h := (hZ.hasSubgaussianMGF_sub_of_abs_sub_le hc).mgf_le t
  simpa [Real.norm_eq_abs, sq_abs] using h

-- Test section: the conditional Hoeffding lemma. With the trivial σ-algebra it is Hoeffding's
-- lemma for a centred random variable with values in `[-c, c]`.
example {X : Ω → ℝ} {c : ℝ} (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, |X ω| ≤ c)
    (h0 : ∫ ω, X ω ∂μ = 0) (t : ℝ) : mgf X μ t ≤ exp (c ^ 2 * t ^ 2 / 2) := by
  have h := condExp_exp_mul_le_of_abs_le (m := ⊥) bot_le hX hb
    (by rw [condExp_bot, h0]; rfl) t
  rw [condExp_bot] at h
  obtain ⟨_, h⟩ := h.exists
  exact h

-- On a standard Borel space the conditional Hoeffding lemma feeds Mathlib's Azuma-Hoeffding
-- inequality: increments with values in `[-1, 1]` and zero conditional mean give
-- `exp (-ε² / (2 n))`.
example [StandardBorelSpace Ω] {Y : ℕ → Ω → ℝ} (hY : StronglyAdapted ℱ Y)
    (hb : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (-1) 1) (h0 : ∫ ω, Y 0 ω ∂μ = 0)
    (hc : ∀ i, μ[Y (i + 1) | ℱ i] =ᵐ[μ] 0) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ≤ exp (-ε ^ 2 / (2 * n)) := by
  -- The parameter `((1 - (-1)) / 2) ^ 2` of the interval `[-1, 1]` is `1`.
  have hp : (‖(1 : ℝ) - -1‖₊ / 2) ^ 2 = 1 := by
    ext
    norm_num
  have hmeas (i : ℕ) : AEMeasurable (Y i) μ := ((hY i).mono (ℱ.le i)).aemeasurable
  have hY0 := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hmeas 0) (hb 0) h0
  rw [hp] at hY0
  have h := measure_sum_ge_le_of_hasCondSubgaussianMGF (cY := fun _ ↦ 1) hY hY0 n
    (fun i _ ↦ hp ▸ hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero (ℱ.le i) (hmeas (i + 1))
      (hb (i + 1)) (hc i)) hε
  simpa using h

end MathlibExtTest.AzumaInequality
