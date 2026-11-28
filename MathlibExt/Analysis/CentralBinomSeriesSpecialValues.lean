/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Real
import MathlibExt.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal
import MathlibExt.Analysis.SpecialFunctions.Log.AlternatingHarmonic

/-!
# Special values of central binomial and harmonic series

The inverse central binomial series in Theorem 8 is the value at `1` of the power series
for `(arcsin x) ^ 2 / 2` on `|x| ≤ 1`. The other evaluation follows by pairing consecutive
terms in finite partial sums of the alternating harmonic series.

## References

* Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of Nörlund*,
  INTEGERS **25** (2025), Article A18, pp. 1–12, Theorem 8, identities (17) and (18).
* D. H. Lehmer, *Interesting Series Involving the Central Binomial Coefficient*,
  The American Mathematical Monthly **92** (1985), pp. 449–457, equation (13).
* The interior arcsine calculation uses `arcsin_central_binomial_reciprocal_series` from
  `MathlibExt.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal` and follows the
  integration argument in `e22A_eq_arcsin_sq` in
  `MathlibExt.Analysis.Ramanujan.Part1Ch9Entry22Chudnovsky`, using central binomial coefficients
  and a summable bound obtained directly from Lehmer's series.
-/

open Filter Finset Set
open scoped Topology

namespace MetaMathlibExt

private noncomputable def firstCoeff (n : ℕ) : ℝ :=
  (4 : ℝ) ^ n / (((n : ℝ) + 1) * (n + 1).centralBinom)

private noncomputable def squareCoeff (n : ℕ) : ℝ := firstCoeff n / ((n : ℝ) + 1)

private lemma firstCoeff_nonneg (n : ℕ) : 0 ≤ firstCoeff n := by
  unfold firstCoeff
  positivity

private lemma squareCoeff_nonneg (n : ℕ) : 0 ≤ squareCoeff n :=
  div_nonneg (firstCoeff_nonneg n) (by positivity)

private lemma firstCoeff_sub (n : ℕ) :
    firstCoeff n - firstCoeff (n + 1) = firstCoeff n / (2 * (n : ℝ) + 3) := by
  have hrec : (((n + 1 : ℕ) : ℝ) + 1) * ((n + 1 + 1).centralBinom : ℝ) =
      2 * (2 * ((n + 1 : ℕ) : ℝ) + 1) * ((n + 1).centralBinom : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ (n + 1)
  have hb : ((n + 1).centralBinom : ℝ) ≠ 0 := by
    exact_mod_cast Nat.centralBinom_ne_zero (n + 1)
  rw [show firstCoeff (n + 1) = (4 : ℝ) ^ (n + 1) /
      ((((n + 1 : ℕ) : ℝ) + 1) * ((n + 1 + 1).centralBinom : ℝ)) by rfl, hrec]
  unfold firstCoeff
  push_cast
  rw [pow_succ]
  field_simp
  ring

-- The endpoint coefficients are bounded by a telescoping series.
private lemma summable_squareCoeff : Summable squareCoeff := by
  apply summable_of_sum_range_le squareCoeff_nonneg (c := 3 * firstCoeff 0)
  intro N
  calc
    ∑ n ∈ range N, squareCoeff n ≤ ∑ n ∈ range N, 3 * (firstCoeff n - firstCoeff (n + 1)) := by
      apply sum_le_sum
      intro n _
      rw [squareCoeff, firstCoeff_sub, ← mul_div_assoc]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [mul_nonneg (firstCoeff_nonneg n) (Nat.cast_nonneg (α := ℝ) n)]
    _ = 3 * (firstCoeff 0 - firstCoeff N) := by rw [← mul_sum, sum_range_sub']
    _ ≤ 3 * firstCoeff 0 := by linarith [firstCoeff_nonneg N]

private noncomputable def squareTerm (n : ℕ) (x : ℝ) : ℝ := squareCoeff n * x ^ (2 * n + 2)

private noncomputable def derivTerm (n : ℕ) (x : ℝ) : ℝ :=
  2 * firstCoeff n * x ^ (2 * n + 1)

private lemma hasDerivAt_squareTerm (n : ℕ) (x : ℝ) :
    HasDerivAt (squareTerm n) (derivTerm n x) x := by
  refine ((hasDerivAt_pow (2 * n + 2) x).const_mul (squareCoeff n)).congr_deriv ?_
  rw [derivTerm, squareCoeff, show 2 * n + 2 - 1 = 2 * n + 1 by omega]
  push_cast
  field_simp

private lemma hasSum_derivTerm {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n => derivTerm n x) (Real.arcsin x / Real.sqrt (1 - x ^ 2)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [derivTerm, zero_pow (Nat.succ_ne_zero _)]
  have h := (arcsin_central_binomial_reciprocal_series x hx).div_const (2 * x)
  convert h using 1
  · funext n
    have hxpow : (2 * x) ^ (2 * (n + 1)) = (4 : ℝ) ^ n * 4 * (x ^ (2 * n + 1) * x) := by
      rw [mul_pow, pow_mul (2 : ℝ), show (2 : ℝ) ^ 2 = 4 by norm_num, pow_succ (4 : ℝ),
        show 2 * (n + 1) = (2 * n + 1) + 1 by omega, pow_succ x]
    have hb : ((n + 1).centralBinom : ℝ) ≠ 0 := by
      exact_mod_cast Nat.centralBinom_ne_zero (n + 1)
    rw [derivTerm, firstCoeff, hxpow, ← Nat.centralBinom_eq_two_mul_choose]
    push_cast
    field_simp
    ring
  · rw [div_mul_eq_mul_div, mul_div_assoc (2 * x),
      mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero hx0)]

private lemma hasDerivAt_squareSeries {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y => ∑' n, squareTerm n y) (Real.arcsin x / Real.sqrt (1 - x ^ 2)) x := by
  obtain ⟨r, hxr, hr1⟩ := exists_between (abs_lt.mpr hx)
  have hr0 : 0 < r := (abs_nonneg x).trans_lt hxr
  have hr : |r| < 1 := by simpa only [abs_of_pos hr0] using hr1
  have hu := (hasSum_derivTerm hr).summable
  have hsum0 : Summable (fun n => squareTerm n 0) := by
    simp [squareTerm]
  have hd := hasDerivAt_tsum_of_isPreconnected hu (t := Ioo (-r) r) isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => hasDerivAt_squareTerm n y) (fun n y hy => ?_) (by simp [hr0]) hsum0
    (abs_lt.mp hxr)
  · rwa [(hasSum_derivTerm (abs_lt.mpr hx)).tsum_eq] at hd
  · have hcoeff : 0 ≤ 2 * firstCoeff n := mul_nonneg zero_le_two (firstCoeff_nonneg n)
    rw [derivTerm, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hcoeff,
      derivTerm]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg y) (abs_lt.mpr hy).le _) hcoeff

private lemma squareSeries_eq_arcsin_sq :
    EqOn (fun x => ∑' n, squareTerm n x) (fun x => Real.arcsin x ^ 2 / 2) (Ioo (-1 : ℝ) 1) := by
  have hd (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt (fun y => Real.arcsin y ^ 2 / 2) (Real.arcsin x / Real.sqrt (1 - x ^ 2)) x := by
    refine (((Real.hasDerivAt_arcsin hx.1.ne' hx.2.ne).pow 2).div_const 2).congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring
  refine isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo
    (fun x hx => (hasDerivAt_squareSeries hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hasDerivAt_squareSeries hx).deriv.trans (hd x hx).deriv.symm)
    (x := 0) (by norm_num) ?_
  simp [squareTerm]

private lemma tsum_squareCoeff : ∑' n, squareCoeff n = Real.pi ^ 2 / 8 := by
  have hs : ContinuousOn (fun x => ∑' n, squareTerm n x) (Icc (-1 : ℝ) 1) := by
    apply continuousOn_tsum (u := squareCoeff) (fun n => ?_) summable_squareCoeff
    · intro n x hx
      rw [squareTerm, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (squareCoeff_nonneg n)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (pow_le_one₀ (abs_nonneg x) (abs_le.mpr hx) (n := 2 * n + 2)) (squareCoeff_nonneg n)
    · unfold squareTerm
      fun_prop
  have heq := squareSeries_eq_arcsin_sq.of_subset_closure hs (by fun_prop) Ioo_subset_Icc_self
    (by rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)])
  have h := heq (right_mem_Icc.mpr (by norm_num : (-1 : ℝ) ≤ 1))
  calc
    ∑' n, squareCoeff n = Real.arcsin 1 ^ 2 / 2 := by simpa [squareTerm] using h
    _ = Real.pi ^ 2 / 8 := by rw [Real.arcsin_one]; ring

private lemma hasSum_odd_mul_succ_reciprocal :
    HasSum (fun n : ℕ => 1 / ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1))) (2 * Real.log 2) := by
  let a (n : ℕ) : ℝ := (-1 : ℝ) ^ n / ((n : ℝ) + 1)
  have hpair (n : ℕ) :
      2 * (a (2 * n) + a (2 * n + 1)) = 1 / ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) := by
    dsimp only [a]
    rw [pow_succ (-1 : ℝ), pow_mul (-1 : ℝ)]
    norm_num only [neg_sq, one_pow, one_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one]
    field_simp
    ring
  have hsum (N : ℕ) :
      (∑ n ∈ range N, 1 / ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1))) =
        2 * ∑ n ∈ range (2 * N), a n := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega, sum_range_succ,
        sum_range_succ (n := 2 * N + 1), sum_range_succ (n := 2 * N), ih, ← hpair]
      ring
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun _ => by positivity) _).2
  simp only [hsum]
  have hdouble : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n (by decide : 0 < 2)) tendsto_id
  exact (Real.tendsto_sum_alternating_harmonic.comp hdouble).const_mul 2

/-- **Central binomial series for $\pi^2/8$ and a series for $2\ln 2$.** We have
$$\sum_{n=0}^{\infty} \frac{4^n}{\binom{2(n+1)}{n+1} (n+1)^2} = \frac{\pi^2}{8}$$
and
$$\sum_{n=0}^{\infty} \frac{1}{(2n+1)(n+1)} = 2\ln 2.$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 8, identities (17) and (18)
(`integers-2025-A18-thm-8`). -/
public theorem tsum_four_pow_div_centralBinom_mul_sq_special :
    ∑' n : ℕ, (4 : ℝ) ^ n / (((n + 1).centralBinom : ℝ) * ((n : ℝ) + 1) ^ 2) = Real.pi ^ 2 / 8 ∧
      ∑' n : ℕ, 1 / ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) = 2 * Real.log 2 := by
  refine ⟨?_, hasSum_odd_mul_succ_reciprocal.tsum_eq⟩
  rw [← tsum_squareCoeff]
  apply tsum_congr
  intro n
  rw [squareCoeff, firstCoeff, div_div, pow_two]
  congr 1
  ac_rfl

end MetaMathlibExt
