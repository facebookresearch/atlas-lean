/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Concentration.McDiarmidPi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Probability.Concentration.McDiarmidPi` -/

namespace MathlibExtTest.McDiarmidPi

open MeasureTheory ProbabilityTheory

open scoped NNReal

-- Test section: bounded differences give a bounded function. The number of `true` coordinates of
-- a pair of booleans changes by at most `1` when one coordinate changes, so two values differ by
-- at most `2`.
example (x y : Fin 2 → Bool) :
    |((if x 0 then 1 else 0) + (if x 1 then 1 else 0) : ℝ) -
      ((if y 0 then 1 else 0) + (if y 1 then 1 else 0))| ≤ 2 := by
  have h := abs_sub_le_sum_of_bounded_differences
    (f := fun x : Fin 2 → Bool => ((if x 0 then 1 else 0) + (if x 1 then 1 else 0) : ℝ))
    (c := fun _ => 1) (fun x i y => by
      fin_cases i <;> cases y <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
        simp [h0, h1]) x y
  simpa [Fin.sum_univ_two, one_add_one_eq_two] using h

-- Test section: Hoeffding's inequality for the sum of `n` independent copies of a measurable
-- function with values in `[0, 1]` is the case `c i = 1` of McDiarmid's inequality.
example {𝓧 : Type*} [MeasurableSpace 𝓧] (P : Measure 𝓧) [IsProbabilityMeasure P] {n : ℕ}
    {g : 𝓧 → ℝ} (hg : Measurable g) (hg01 : ∀ y, g y ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin n => P).real
        {x | ε ≤ ∑ k, g (x k) - ∫ x', ∑ k, g (x' k) ∂(Measure.pi fun _ : Fin n => P)} ≤
      Real.exp (-2 * ε ^ 2 / n) := by
  have h := measureReal_sub_integral_ge_le_of_bounded_differences (μ := fun _ : Fin n => P)
    (f := fun x => ∑ k, g (x k)) (c := fun _ => 1) (by fun_prop) (fun x k y => by
      have hsum : ∑ j, g (Function.update x k y j) - ∑ j, g (x j) = g y - g (x k) := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single k]
        · simp
        · intro j _ hj
          simp [Function.update_of_ne hj]
        · simp
      rw [hsum, NNReal.coe_one, abs_le]
      constructor <;> linarith [(hg01 y).1, (hg01 y).2, (hg01 (x k)).1, (hg01 (x k)).2]) hε
  simpa using h

-- The lower tail, for a product of two different probability measures.
example {𝓧 : Type*} [MeasurableSpace 𝓧] (μ₀ μ₁ : Measure 𝓧) [IsProbabilityMeasure μ₀]
    [IsProbabilityMeasure μ₁] (f : (Fin 2 → 𝓧) → ℝ) (hf : Measurable f) (c : Fin 2 → ℝ≥0)
    (hfc : ∀ x i y, |f (Function.update x i y) - f x| ≤ c i) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi ![μ₀, μ₁]).real {x | ε ≤ ∫ y, f y ∂Measure.pi ![μ₀, μ₁] - f x} ≤
      Real.exp (-2 * ε ^ 2 / ((c 0 : ℝ) ^ 2 + (c 1 : ℝ) ^ 2)) := by
  have : ∀ i, IsProbabilityMeasure (![μ₀, μ₁] i) := by
    intro i
    fin_cases i
    · exact ‹IsProbabilityMeasure μ₀›
    · exact ‹IsProbabilityMeasure μ₁›
  simpa [Fin.sum_univ_two] using measureReal_integral_sub_ge_le_of_bounded_differences hf hfc hε

-- Test section: the zero-sensitivity endpoint. A measurable function whose value never changes
-- when one coordinate changes has a sub-Gaussian moment-generating function with parameter `0`,
-- so it is almost surely equal to its mean.
example {𝓧 : Type*} [MeasurableSpace 𝓧] (P : Measure 𝓧) [IsProbabilityMeasure P] {n : ℕ}
    {f : (Fin n → 𝓧) → ℝ} (hf : Measurable f)
    (hfc : ∀ x i y, f (Function.update x i y) = f x) :
    (fun x => f x - ∫ y, f y ∂Measure.pi fun _ : Fin n => P) =ᵐ[Measure.pi fun _ : Fin n => P]
      0 := by
  have h := hasSubgaussianMGF_sub_integral_of_bounded_differences (μ := fun _ : Fin n => P)
    (c := fun _ => 0) hf fun x i y => by simp [hfc]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    Finset.sum_const_zero] at h
  exact h.ae_eq_zero_of_hasSubgaussianMGF_zero

-- The sub-Gaussian parameter is `∑ i, c i ^ 2 / 4`: for one coordinate of sensitivity `1`, the
-- moment-generating function of `f - E[f]` is at most `exp (t ^ 2 / 8)`, Hoeffding's lemma for a
-- variable with values in an interval of length `1`.
example {𝓧 : Type*} [MeasurableSpace 𝓧] (P : Measure 𝓧) [IsProbabilityMeasure P]
    {f : (Fin 1 → 𝓧) → ℝ} (hf : Measurable f)
    (hfc : ∀ x i y, |f (Function.update x i y) - f x| ≤ 1) (t : ℝ) :
    mgf (fun x => f x - ∫ y, f y ∂Measure.pi fun _ : Fin 1 => P)
      (Measure.pi fun _ : Fin 1 => P) t ≤ Real.exp (t ^ 2 / 8) := by
  refine ((hasSubgaussianMGF_sub_integral_of_bounded_differences (μ := fun _ : Fin 1 => P)
    (c := fun _ => 1) hf fun x i y => by simpa using hfc x i y).mgf_le t).trans_eq ?_
  congr 1
  norm_num
  ring

end MathlibExtTest.McDiarmidPi
