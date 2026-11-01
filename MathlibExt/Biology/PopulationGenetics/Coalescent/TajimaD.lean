/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Tajima
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Tajima's `D` and a conservative Chebyshev test of neutrality

For a sample of `n` genes with `S` segregating sites and mean number of pairwise differences
`π`, **Tajima's `D`** (Tajima 1989) is

`D = (π - S / a₁) / √(e₁ S + e₂ S (S - 1))`,

where the denominator is the square root of the unbiased estimator of
`Var(π - S / a₁) = c₁ θ + c₂ θ²` (`Coalescent/Tajima.lean`, `Coalescent/TajimaVariance.lean`).

* For `n = 2` and `n = 3` the constants `c₁, c₂` vanish (with two or three genes and infinite
  sites, `π = S / a₁` identically), so `D` is undefined there; for `n ≥ 4` both are positive,
  hence the denominator is positive as soon as `S ≥ 1`.
* Tajima compared `D` with a beta distribution fitted to its range; that law is an
  approximation and is not formalized. We formalize instead the exact, conservative
  **Chebyshev test** at a known (hypothesized) `θ₀`: reject neutrality when
  `|π - S / a₁| ≥ √((c₁ θ₀ + c₂ θ₀²) / α)`. Its level is at most `α` whenever the numerator has
  mean `0` and variance `c₁ θ₀ + c₂ θ₀²`, which are the conclusions of
  `KingmanTimes.integral_tajimaNumerator` and `KingmanTimes.variance_tajimaNumerator` under the
  standard neutral model.

The test is stated for a known `θ₀`; `D` itself, with the estimated denominator, has no exact
finite-sample guarantee from Chebyshev's inequality and none is claimed.

## Main results

* `tajimaD`: Tajima's `D`.
* `tajimaC1_two`, `tajimaC2_two`, `tajimaC1_three`, `tajimaC2_three`: the degenerate sample
  sizes.
* `tajimaC1_pos`, `tajimaC2_pos`: `c₁ > 0` and `c₂ > 0` for `n ≥ 4`.
* `tajimaVarEstimator_pos`: `e₁ S + e₂ S (S - 1) > 0` for `n ≥ 4` and `S ≥ 1`.
* `measure_tajimaChebyshevTest_le`: the Chebyshev test has level at most `α`.

## References

* F. Tajima, *Statistical method for testing the neutral mutation hypothesis by DNA
  polymorphism*, Genetics 123 (1989), 585–595.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

/-- **Tajima's `D`** (Tajima 1989) for a sample of `n` genes with mean number of pairwise
differences `π` and `S` segregating sites:
`D = (π - S / a₁) / √(e₁ S + e₂ S (S - 1))`. It is meaningful for `n ≥ 4` and `S ≥ 1`
(`tajimaVarEstimator_pos`); otherwise Lean's junk values for `x / 0` and `√` of a nonpositive
number apply. -/
def tajimaD (n : ℕ) (π S : ℝ) : ℝ :=
  (π - S / tajimaA1 n) / Real.sqrt (tajimaE1 n * S + tajimaE2 n * (S * (S - 1)))

/-- For two genes `c₁ = 0`. -/
theorem tajimaC1_two : tajimaC1 2 = 0 := by
  simp [tajimaC1, tajimaB1, tajimaA1]
  norm_num

/-- For two genes `c₂ = 0`. -/
theorem tajimaC2_two : tajimaC2 2 = 0 := by
  simp [tajimaC2, tajimaB2, tajimaA1, tajimaA2]
  norm_num

/-- For three genes `c₁ = 0`. -/
theorem tajimaC1_three : tajimaC1 3 = 0 := by
  simp [tajimaC1, tajimaB1, tajimaA1, sum_Ico_succ_top]
  norm_num

/-- For three genes `c₂ = 0`. -/
theorem tajimaC2_three : tajimaC2 3 = 0 := by
  simp [tajimaC2, tajimaB2, tajimaA1, tajimaA2, sum_Ico_succ_top]
  norm_num

private theorem tajimaA1_succ {n : ℕ} (hn : 1 ≤ n) :
    tajimaA1 (n + 1) = tajimaA1 n + (n : ℝ)⁻¹ :=
  sum_Ico_succ_top hn _

private theorem tajimaA1_mono {m n : ℕ} (h : m ≤ n) : tajimaA1 m ≤ tajimaA1 n :=
  sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right h) fun i _ _ => by positivity

private theorem tajimaA2_mono {m n : ℕ} (h : m ≤ n) : tajimaA2 m ≤ tajimaA2 n :=
  sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right h) fun i _ _ => by positivity

private theorem tajimaA1_four : tajimaA1 4 = 11 / 6 := by
  simp [tajimaA1, sum_Ico_succ_top]
  norm_num

private theorem tajimaA1_five : tajimaA1 5 = 25 / 12 := by
  simp [tajimaA1, sum_Ico_succ_top]
  norm_num

private theorem tajimaA2_four : tajimaA2 4 = 49 / 36 := by
  simp [tajimaA2, sum_Ico_succ_top]
  norm_num

/-- `a₁(n) + 2 / n > 2` for `n ≥ 4`. -/
private theorem tajimaA1_add_gt {n : ℕ} (hn : 4 ≤ n) : 2 < tajimaA1 n + 2 / n := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  rcases Nat.lt_or_ge n 5 with h | h
  · have : n = 4 := by omega
    subst this
    rw [tajimaA1_four]
    norm_num
  · have := tajimaA1_mono h
    rw [tajimaA1_five] at this
    have : 0 < 2 / (n : ℝ) := by positivity
    linarith

/-- `3 (n - 1) < (n + 1) a₁(n)` for `n ≥ 4`. -/
private theorem c1_key {n : ℕ} (hn : 4 ≤ n) : 3 * ((n : ℝ) - 1) < ((n : ℝ) + 1) * tajimaA1 n := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [tajimaA1_four]
    norm_num
  | succ n hn ih =>
    rw [tajimaA1_succ (by omega)]
    have h2 := tajimaA1_add_gt hn
    have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hx : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have h2' : 2 < tajimaA1 n + 2 * (n : ℝ)⁻¹ := by rwa [div_eq_mul_inv] at h2
    push_cast
    nlinarith

/-- `c₁ = (n + 1) / (3 (n - 1)) - 1 / a₁ > 0` for `n ≥ 4`. -/
theorem tajimaC1_pos {n : ℕ} (hn : 4 ≤ n) : 0 < tajimaC1 n := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < tajimaA1 n := by
    have := tajimaA1_mono hn
    rw [tajimaA1_four] at this
    linarith
  have hk := c1_key hn
  unfold tajimaC1 tajimaB1
  rw [sub_pos, div_lt_div_iff₀ ha (by linarith)]
  linarith


/-- `c₂ = b₂ - (n + 2) / (a₁ n) + a₂ / a₁² > 0` for `n ≥ 4`. -/
theorem tajimaC2_pos {n : ℕ} (hn : 4 ≤ n) : 0 < tajimaC2 n := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < tajimaA1 n := by
    have := tajimaA1_mono hn
    rw [tajimaA1_four] at this
    linarith
  have ha2 : 49 / 36 ≤ tajimaA2 n := by
    have := tajimaA2_mono hn
    rwa [tajimaA2_four] at this
  have hc : tajimaC2 n = (tajimaB2 n * tajimaA1 n ^ 2 - ((n : ℝ) + 2) / n * tajimaA1 n +
      tajimaA2 n) / tajimaA1 n ^ 2 := by
    unfold tajimaC2
    field_simp
  set x := tajimaA1 n
  set y := tajimaA2 n
  set N : ℝ := (n : ℝ) with hN
  have hb : 0 < tajimaB2 n := by unfold tajimaB2; apply div_pos <;> nlinarith
  set b := tajimaB2 n with hbdef
  set B : ℝ := (N + 2) / N
  have hcub : 0 < 17 * N ^ 3 - 145 * N ^ 2 + 294 * N + 324 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ N - 4) (sq_nonneg (N - 5)),
      sq_nonneg (N - 811 / 186)]
  have hdisc : B ^ 2 < 4 * b * y := by
    have hb' : b = 2 * (N ^ 2 + N + 3) / (9 * N * (N - 1)) := rfl
    rw [hb']
    simp only [B]
    rw [div_pow, div_lt_iff₀ (by positivity)]
    rw [show 4 * (2 * (N ^ 2 + N + 3) / (9 * N * (N - 1))) * y * N ^ 2 =
      8 * (N ^ 2 + N + 3) * y * N / (9 * (N - 1)) by field_simp; ring]
    rw [lt_div_iff₀ (by linarith)]
    have h1 : 8 * (N ^ 2 + N + 3) * N * (49 / 36) ≤ 8 * (N ^ 2 + N + 3) * N * y :=
      mul_le_mul_of_nonneg_left ha2 (by positivity)
    nlinarith [h1, hcub]
  have hq : 0 < b * x ^ 2 - B * x + y := by
    nlinarith [sq_nonneg (2 * b * x - B)]
  rw [hc]
  positivity


/-- The denominator of Tajima's `D` is well defined: `e₁ S + e₂ S (S - 1) > 0` for `n ≥ 4` and
`S ≥ 1`. -/
theorem tajimaVarEstimator_pos {n : ℕ} (hn : 4 ≤ n) {S : ℝ} (hS : 1 ≤ S) :
    0 < tajimaE1 n * S + tajimaE2 n * (S * (S - 1)) := by
  have ha1 : 0 < tajimaA1 n := by
    rw [tajimaA1_eq_harmonic]
    exact_mod_cast harmonic_pos (by omega)
  have ha2 : 0 ≤ tajimaA2 n := sum_nonneg fun i _ => by positivity
  have he1 : 0 < tajimaE1 n := div_pos (tajimaC1_pos hn) ha1
  have he2 : 0 < tajimaE2 n := div_pos (tajimaC2_pos hn) (by positivity)
  have hSS : 0 ≤ S * (S - 1) := mul_nonneg (by linarith) (by linarith)
  have := mul_nonneg he2.le hSS
  nlinarith

/-- The rejection region of the **Chebyshev test of neutrality** at level `α` and hypothesized
`θ₀`: `|π - S / a₁| ≥ √((c₁ θ₀ + c₂ θ₀²) / α)`. -/
def tajimaChebyshevTest (n : ℕ) (θ₀ α π S : ℝ) : Prop :=
  Real.sqrt ((tajimaC1 n * θ₀ + tajimaC2 n * θ₀ ^ 2) / α) ≤ |π - S / tajimaA1 n|

/-- **Level of the Chebyshev test**: if Tajima's numerator `π - S / a₁` is square integrable
with mean `0` and variance `c₁ θ₀ + c₂ θ₀² > 0` (as under the standard neutral model, by
`KingmanTimes.integral_tajimaNumerator` and `KingmanTimes.variance_tajimaNumerator`), then for
every `α > 0` the test rejects with probability at most `α`. -/
theorem measure_tajimaChebyshevTest_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {π S : Ω → ℝ} {θ₀ α : ℝ} (hα : 0 < α)
    (hmem : MemLp (fun ω => π ω - S ω / tajimaA1 n) 2 μ)
    (hmean : μ[fun ω => π ω - S ω / tajimaA1 n] = 0)
    (hvar : Var[fun ω => π ω - S ω / tajimaA1 n; μ] = tajimaC1 n * θ₀ + tajimaC2 n * θ₀ ^ 2)
    (hpos : 0 < tajimaC1 n * θ₀ + tajimaC2 n * θ₀ ^ 2) :
    μ {ω | tajimaChebyshevTest n θ₀ α (π ω) (S ω)} ≤ ENNReal.ofReal α := by
  set v := tajimaC1 n * θ₀ + tajimaC2 n * θ₀ ^ 2 with hv
  have hε : 0 < Real.sqrt (v / α) := Real.sqrt_pos.mpr (div_pos hpos hα)
  have hset : {ω | tajimaChebyshevTest n θ₀ α (π ω) (S ω)} =
      {ω | Real.sqrt (v / α) ≤
        |(fun ω => π ω - S ω / tajimaA1 n) ω - μ[fun ω => π ω - S ω / tajimaA1 n]|} := by
    ext ω
    simp [tajimaChebyshevTest, hmean, hv]
  rw [hset]
  refine (meas_ge_le_variance_div_sq hmem hε).trans (le_of_eq ?_)
  rw [hvar, Real.sq_sqrt (div_pos hpos hα).le, div_div_cancel₀ hpos.ne']

end MathlibExt.Biology.PopulationGenetics.Coalescent
