/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.LinearNeutralityTest
public import MathlibExt.Probability.Distributions.PoissonKernel
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Tests for general linear neutrality tests and weight-consistent scaling

A witness with a genuinely random spectrum for three sequences (a `Po(2)` count of singletons
and one doubleton, the neutral means for `θ = 1 / 2` per base and length `L = 4`), on which the
test of the weights `(1, -1)` is `(ξ₁ - 2) / √2`, centred and of variance `1`; the
characterization of centred, unit-variance linear statistics on it; rescaled weights; the two
forms of Fay and Wu's weights for four sequences; junk values; the cutoff example (the centred
weights of `2 (1 - f) - c / f` change sign with `c`, the normalized ones do not depend on `c`);
and the `O(1 / n)` bounds for Fay and Wu's weight functions and for a weight function with a
jump.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.LinearNeutralityTest

open MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFS
open MathlibExt.Biology.PopulationGenetics.Coalescent.LinearNeutralityTest

/-! ### A Poisson witness for three sequences -/

section Poisson

/-- Three sequences: `ξ 1` is a `Po(2)` count of singletons and there is always exactly one
doubleton, so `E ξ_i = θ L / i` for `θ L = 2`. -/
noncomputable def xiPo (i : ℕ) (k : ℕ) : ℝ :=
  if i = 1 then (k : ℝ) else if i = 2 then 1 else 0

/-- The weights `(1, -1)`. -/
def wPo (i : ℕ) : ℝ := if i = 1 then 1 else if i = 2 then -1 else 0

lemma Ico_one_three : (Ico 1 3 : Finset ℕ) = {1, 2} := by decide

lemma integrable_xiPo (i : ℕ) : Integrable (xiPo i) (poissonMeasure 2) := by
  unfold xiPo
  split_ifs
  · exact integrable_natCast_poissonMeasure 2
  · exact integrable_const _
  · exact integrable_const _

/-- The neutral means for `θ = 1 / 2` per base and sequence length `L = 4`. -/
lemma integral_xiPo :
    ∀ i ∈ (Ico 1 3 : Finset ℕ), (poissonMeasure 2)[xiPo i] = 1 / 2 * 4 / (i : ℝ) := by
  intro i hi
  rw [Ico_one_three] at hi
  rcases mem_insert.1 hi with rfl | hi
  · simp only [xiPo, ↓reduceIte, integral_natCast_poissonMeasure]
    norm_num
  · rw [mem_singleton.1 hi]
    simp only [xiPo, OfNat.ofNat_ne_one, ↓reduceIte, integral_const, probReal_univ, smul_eq_mul]
    norm_num

lemma sum_wPo : ∑ i ∈ Ico 1 3, wPo i = 0 := by
  simp [Ico_one_three, wPo]

/-- The numerator `ξ₁ - 2 ξ₂ = ξ₁ - 2`. -/
lemma thetaWeighted_wPo : thetaWeighted 3 wPo xiPo = fun k : ℕ => (k : ℝ) - 2 := by
  funext k
  simp only [thetaWeighted, Ico_one_three, wPo, xiPo]
  rw [sum_pair (by norm_num)]
  norm_num
  ring

/-- The numerator has the variance `2` of a `Po(2)` count. -/
lemma variance_thetaWeighted_wPo : Var[thetaWeighted 3 wPo xiPo; poissonMeasure 2] = 2 := by
  rw [thetaWeighted_wPo, variance_sub_const (by fun_prop), variance_natCast_poissonMeasure]
  norm_num

/-- **Non-vacuity**: the test of `(1, -1)` is centred under the witness. -/
example : (poissonMeasure 2)[linearNeutralityTest (poissonMeasure 2) 3 wPo xiPo] = 0 :=
  integral_linearNeutralityTest integrable_xiPo integral_xiPo sum_wPo

/-- **Non-vacuity**: the test of `(1, -1)` has variance `1` under the witness. -/
example : Var[linearNeutralityTest (poissonMeasure 2) 3 wPo xiPo; poissonMeasure 2] = 1 :=
  variance_linearNeutralityTest (by rw [variance_thetaWeighted_wPo]; norm_num)

/-- The test itself is `(ξ₁ - 2) / √2`. -/
example :
    linearNeutralityTest (poissonMeasure 2) 3 wPo xiPo = fun k : ℕ => ((k : ℝ) - 2) / √2 := by
  funext k
  simp only [linearNeutralityTest, variance_thetaWeighted_wPo]
  rw [thetaWeighted_wPo]

/-- Weights `(3, -3)` give the same test (`linearNeutralityTest_const_mul`). -/
example : linearNeutralityTest (poissonMeasure 2) 3 (fun i => 3 * wPo i) xiPo =
    linearNeutralityTest (poissonMeasure 2) 3 wPo xiPo :=
  linearNeutralityTest_const_mul (by norm_num) wPo

/-- **Characterization**: `(ξ₁ - 2 ξ₂) / √2` has mean `0` and variance `1`, so it is a test
`T_W` with weights summing to `0` (`exists_linearNeutralityTest_eq_iff`). -/
example : ∃ W : ℕ → ℝ, ∑ i ∈ Ico 1 3, W i = 0 ∧
    Var[thetaWeighted 3 W xiPo; poissonMeasure 2] ≠ 0 ∧
    linearNeutralityTest (poissonMeasure 2) 3 W xiPo =
      fun k => ∑ i ∈ Ico 1 3, (wPo i * i / √2) * xiPo i k := by
  have hS : (fun k => ∑ i ∈ Ico 1 3, (wPo i * i / √2) * xiPo i k) =
      fun k : ℕ => (√2)⁻¹ * ((k : ℝ) - 2) := by
    funext k
    simp only [Ico_one_three, wPo, xiPo]
    rw [sum_pair (by norm_num)]
    norm_num
    ring
  refine (exists_linearNeutralityTest_eq_iff integrable_xiPo (by norm_num) integral_xiPo _).2
    ⟨?_, ?_⟩
  · rw [hS, integral_const_mul, integral_sub (integrable_natCast_poissonMeasure 2)
      (integrable_const _), integral_natCast_poissonMeasure]
    simp
  · rw [hS, variance_const_mul, variance_sub_const (by fun_prop),
      variance_natCast_poissonMeasure, inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num

/-- Fay and Wu's `H` for three sequences is `(ξ₁ - 2 ξ₂) / 3`, so its test
(`linearNeutralityTest_fayWuH`) is again `(ξ₁ - 2) / √2`: for `n = 3` every test is that of
`(1, -1)` or of `(-1, 1)`. -/
example : linearNeutralityTest (poissonMeasure 2) 3
    (normalizedWeights (fun _ => 1) (fun f => 2 * f) 3) xiPo =
      fun k : ℕ => ((k : ℝ) - 2) / √2 := by
  rw [(linearNeutralityTest_fayWuH (by norm_num)).1]
  have hH : fayWuH 3 xiPo = fun k : ℕ => (1 / 3 : ℝ) * ((k : ℝ) - 2) := by
    funext k
    simp only [fayWuH, thetaPi, thetaH, thetaWeighted, Ico_one_three]
    rw [sum_pair (by norm_num), sum_pair (by norm_num)]
    norm_num [xiPo, Nat.choose]
    ring
  funext k
  rw [hH, variance_const_mul, variance_sub_const (by fun_prop), variance_natCast_poissonMeasure,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by norm_num)]
  push_cast
  field_simp

end Poisson

/-! ### Weights -/

/-- Fay and Wu's centred weights `1 - 2 i / n` for `n = 4`. -/
example : centredWeights (fun f => 1 - 2 * f) 4 1 = 1 / 2 ∧
    centredWeights (fun f => 1 - 2 * f) 4 2 = 0 ∧
    centredWeights (fun f => 1 - 2 * f) 4 3 = -1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [centredWeights, sum_Ico_succ_top]

/-- Fay and Wu's normalized weights `(n - 2 i) / (n (n - 1))` for `n = 4`: the centred weights
divided by `n - 1 = 3`. -/
example : normalizedWeights (fun _ => 1) (fun f => 2 * f) 4 1 = 1 / 6 ∧
    normalizedWeights (fun _ => 1) (fun f => 2 * f) 4 2 = 0 ∧
    normalizedWeights (fun _ => 1) (fun f => 2 * f) 4 3 = -1 / 6 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [normalizedWeights, sum_Ico_succ_top]

/-- The centred weights of any weight function sum to `0` for `n = 4`. -/
example (W : ℝ → ℝ) : ∑ i ∈ Ico 1 4, centredWeights W 4 i = 0 :=
  sum_centredWeights W (by norm_num)

/-- Junk value: for `n = 1` there is no frequency to average and the centred weights are the
values `W i` (Lean's `i / 1 = i`). -/
example (W : ℝ → ℝ) (i : ℕ) : centredWeights W 1 i = W i := by
  simp [centredWeights]

/-- Junk value: a vanishing normalizing sum makes its term `0`. -/
example (w' : ℝ → ℝ) (i : ℕ) :
    normalizedWeights (fun _ => 0) w' 4 i =
      -(w' ((i : ℝ) / 4) / ∑ j ∈ (Ico 1 4 : Finset ℕ), w' ((j : ℝ) / 4)) := by
  simp [normalizedWeights]

/-! ### The cutoff of a divergent weight function -/

/-- For `n = 3`, the first centred weights of `2 (1 - f) - c / f` for `c = 1 / 4` and `c = 1`
(`centredWeights_tajima_watterson_three_one`). -/
example : centredWeights (fun f => 2 * (1 - f) - (1 / 4) / f) 3 1 = 7 / 48 ∧
    centredWeights (fun f => 2 * (1 - f) - 1 / f) 3 1 = -5 / 12 := by
  rw [centredWeights_tajima_watterson_three_one, centredWeights_tajima_watterson_three_one]
  norm_num

/-- The second centred weight is the negative of the first, as for any centred weights with
`n = 3`. -/
example (c : ℝ) : centredWeights (fun f => 2 * (1 - f) - c / f) 3 2 =
    -centredWeights (fun f => 2 * (1 - f) - c / f) 3 1 := by
  have h := sum_centredWeights (fun f => 2 * (1 - f) - c / f) (n := 3) (by norm_num)
  rw [Ico_one_three, sum_pair (by norm_num)] at h
  linarith

/-- So the weight vectors for `c = 1 / 4` and `c = 1` are related by no positive factor
(`not_exists_centredWeights_three_eq_const_mul`), and in fact by the factor `-20 / 7`. -/
example : (¬ ∃ a : ℝ, 0 < a ∧ ∀ i ∈ Ico 1 3,
      centredWeights (fun f => 2 * (1 - f) - 1 / f) 3 i =
        a * centredWeights (fun f => 2 * (1 - f) - (1 / 4) / f) 3 i) ∧
    centredWeights (fun f => 2 * (1 - f) - 1 / f) 3 1 =
      -20 / 7 * centredWeights (fun f => 2 * (1 - f) - (1 / 4) / f) 3 1 := by
  refine ⟨not_exists_centredWeights_three_eq_const_mul, ?_⟩
  rw [centredWeights_tajima_watterson_three_one, centredWeights_tajima_watterson_three_one]
  norm_num

/-- The normalized weights do not depend on `c ≠ 0` (`normalizedWeights_const_mul`). -/
example (c : ℝ) (hc : c ≠ 0) :
    normalizedWeights (fun f => 2 * (1 - f)) (fun f => c * f⁻¹) 3 =
      normalizedWeights (fun f => 2 * (1 - f)) (fun f => f⁻¹) 3 := by
  simpa using normalizedWeights_const_mul (n := 3) (fun f => 2 * (1 - f)) (fun f => f⁻¹)
    one_ne_zero hc

/-! ### The `O(1 / n)` bounds -/

lemma boundedVariationOn_one : BoundedVariationOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 1) :=
  (monotoneOn_const).boundedVariationOn (C := 1) fun _ _ => by norm_num

lemma boundedVariationOn_two_mul : BoundedVariationOn (fun f : ℝ => 2 * f) (Set.Icc 0 1) := by
  have h : MonotoneOn (fun f : ℝ => 2 * f) (Set.Icc 0 1) := fun _ _ _ _ h => by
    simp only
    linarith
  refine h.boundedVariationOn (C := 2) fun x hx => ?_
  rw [abs_of_nonneg (by linarith [hx.1])]
  linarith [hx.2]

lemma integral_two_mul : ∫ f in (0 : ℝ)..1, 2 * f = 1 := by
  rw [intervalIntegral.integral_const_mul, integral_id]
  norm_num

/-- Fay and Wu's weight functions `w(f) = 1` and `w'(f) = 2 f`: the normalized weights, times
`n`, are within `O(1 / n)` of the centred weights of `1 - 2 f`. -/
example : ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ Ico 1 n,
    |n * normalizedWeights (fun _ => 1) (fun f => 2 * f) n i -
      centredWeights (fun f => 1 - 2 * f) n i| ≤ C / n :=
  exists_abs_mul_normalizedWeights_sub_centredWeights_le boundedVariationOn_one
    boundedVariationOn_two_mul (by simp) integral_two_mul

/-- A weight function with a jump, `-1` up to `1 / 2` and `1` above. -/
noncomputable def stepW (f : ℝ) : ℝ := if f ≤ 1 / 2 then -1 else 1

lemma monotoneOn_stepW : MonotoneOn stepW (Set.Icc 0 1) := by
  intro x _ y _ hxy
  unfold stepW
  split_ifs <;> linarith

lemma integral_stepW : ∫ f in (0 : ℝ)..1, stepW f = 0 := by
  have hI : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → IntervalIntegrable stepW volume a b :=
    fun a b ha hab hb => MonotoneOn.intervalIntegrable (monotoneOn_stepW.mono (by
      rw [Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc ha hb))
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2) (hI 0 (1 / 2) le_rfl
      (by norm_num) (by norm_num)) (hI (1 / 2) 1 (by norm_num) (by norm_num) le_rfl)]
  have h1 : ∫ f in (0 : ℝ)..1 / 2, stepW f = ∫ _ in (0 : ℝ)..1 / 2, (-1 : ℝ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num)] at hx
    simp only [stepW, hx.2, ↓reduceIte]
  have h2 : ∫ f in (1 / 2 : ℝ)..1, stepW f = ∫ _ in (1 / 2 : ℝ)..1, (1 : ℝ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num)] at hx
    simp only [stepW, not_le.2 hx.1, ↓reduceIte]
  rw [h1, h2, intervalIntegral.integral_const, intervalIntegral.integral_const]
  norm_num

/-- The step weight function has bounded variation, and its centred weights are within
`O(1 / n)` of its values at `i / n`, although it is not continuous. -/
example : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ i : ℕ,
    |centredWeights stepW n i - stepW ((i : ℝ) / n)| ≤ C / n :=
  exists_abs_centredWeights_sub_le (monotoneOn_stepW.boundedVariationOn (C := 1) fun x _ => by
    unfold stepW
    split_ifs <;> norm_num) integral_stepW

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.LinearNeutralityTest
