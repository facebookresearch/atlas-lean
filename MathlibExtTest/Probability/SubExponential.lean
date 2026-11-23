/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SubExponential

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace MathlibExtTest.Probability.SubExponential

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Bridge from Mathlib: a centred variable with values in `[a, b]` is sub-Gaussian by Hoeffding's
lemma, hence sub-exponential with parameters `(√((b - a)² / 4), α)` for every `α`, and the
sub-exponential tail bound applies in the Gaussian regime. -/
example {X : Ω → ℝ} (hm : AEMeasurable X μ) {a b : ℝ} (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hc : μ[X] = 0) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ X ω} ≤
      exp (-t ^ 2 / (2 * (NNReal.sqrt ((‖b - a‖₊ / 2) ^ 2) : ℝ) ^ 2)) :=
  ((hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hc).hasSubexponentialMGF 0)
    |>.measureReal_ge_le_of_le ht (by simp; positivity)

/-- The zero variable is sub-exponential with parameters `(0, α)`; the exponential-regime tail bound
then gives `P(0 ≥ t) ≤ exp (-t / (2 α))` for every `t ≥ 0`. -/
example (α : ℝ≥0) (hα : 0 < α) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (0 : Ω → ℝ) ω} ≤ exp (-t / (2 * α)) := by
  have h : HasSubexponentialMGF (0 : Ω → ℝ) 0 α μ := by
    simpa using (HasSubgaussianMGF.zero (μ := μ)).hasSubexponentialMGF α
  exact h.measureReal_ge_le_of_ge hα (by simp; positivity)

/-- Negation: if `X` is sub-exponential with parameters `(ν, α)`, so is `-X`, and the
Gaussian-regime upper-tail bound for `-X` is a lower-tail bound for `X`. -/
example {X : Ω → ℝ} {ν α : ℝ≥0} (h : HasSubexponentialMGF X ν α μ) {t : ℝ} (ht : 0 ≤ t)
    (htα : α * t ≤ ν ^ 2) : μ.real {ω | t ≤ -X ω} ≤ exp (-t ^ 2 / (2 * ν ^ 2)) :=
  h.neg.measureReal_ge_le_of_le ht htα

/-- Image measures: if `Y` sends `μ'` to `μ` and `X` is sub-exponential under `μ`, then `X ∘ Y` is
sub-exponential under `μ'` with the same parameters; here `Y` is the first projection of a product
of probability measures. -/
example {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (μ' : Measure Ω') [IsProbabilityMeasure μ']
    {X : Ω → ℝ} {ν α : ℝ≥0} (h : HasSubexponentialMGF X ν α μ) :
    HasSubexponentialMGF (X ∘ Prod.fst) ν α (μ.prod μ') :=
  .of_map measurable_fst.aemeasurable (by rwa [Measure.map_fst_prod, measure_univ, one_smul])

/-- Bernstein's inequality is applicable to any bounded centred variable; here with the
variance proxy `σ² = b²`, the crude bound `E[X²] ≤ b²`. -/
example {X : Ω → ℝ} (hX : AEMeasurable X μ) {b t : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ b) (hmean : μ[X] = 0) (hvar : ∫ ω, X ω ^ 2 ∂μ ≤ b ^ 2)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * exp (-t ^ 2 / (2 * (b ^ 2 + b * t))) :=
  measureReal_abs_ge_le_bernstein hX hb0 hb hmean hvar ht

/-- The series bound at `y = 0` is an equality, and at `y = 1/2` it reads `exp (1/2) ≤ 7/4`. -/
example : exp (1 / 2 : ℝ) ≤ 7 / 4 := by
  have h := exp_le_one_add_add_sq_div_of_abs_lt_one (y := (1 / 2 : ℝ)) (by norm_num [abs_of_pos])
  norm_num [abs_of_pos] at h
  linarith

/-- The degenerate Bernstein case `σ = 0` (so `X = 0` almost surely) is covered: the bound holds
for the zero variable with `b = 1`. -/
example {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (fun _ : Ω => (0 : ℝ)) ω} ≤ exp (-t ^ 2 / (2 * (0 ^ 2 + 1 * t))) :=
  measureReal_ge_le_bernstein (X := fun _ : Ω => (0 : ℝ)) aemeasurable_const zero_le_one
    (by simp) (by simp) (by simp) ht

end MathlibExtTest.Probability.SubExponential
