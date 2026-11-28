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
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import MathlibExt.Analysis.SpecialFunctions.ArcsinSquareSeries
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
* `hasSum_arcsin_sq_div_two` in `MathlibExt.Analysis.SpecialFunctions.ArcsinSquareSeries`
  gives the interior identity; here a telescoping bound permits evaluation at the endpoint.
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

private lemma squareCoeff_eq (n : ℕ) :
    squareCoeff n = (4 : ℝ) ^ n / (((n + 1).centralBinom : ℝ) * ((n : ℝ) + 1) ^ 2) := by
  rw [squareCoeff, firstCoeff, div_div, pow_two]
  congr 1
  ac_rfl

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
  have hinterior :
      EqOn (fun x => ∑' n, squareTerm n x) (fun x => Real.arcsin x ^ 2 / 2) (Ioo (-1 : ℝ) 1) := by
    intro x hx
    simpa only [squareTerm, squareCoeff_eq] using (hasSum_arcsin_sq_div_two (abs_lt.mpr hx)).tsum_eq
  have heq := hinterior.of_subset_closure hs (by fun_prop) Ioo_subset_Icc_self
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
  simpa only [squareCoeff_eq] using tsum_squareCoeff

end MetaMathlibExt
