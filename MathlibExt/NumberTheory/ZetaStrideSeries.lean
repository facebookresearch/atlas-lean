/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeriesComplex
import MathlibExt.Analysis.SpecialFunctions.Log.AlternatingHarmonic

/-!
# A zeta evaluation of a series with an odd denominator

The first power is evaluated by pairing successive terms of the alternating harmonic series.
A recurrence expresses the higher powers in terms of that value and ordinary zeta values.
-/

namespace MetaMathlibExt

open Filter
open scoped Topology

private theorem hasSum_inv_mul_two_mul_sub_one :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) - 1)))
      (2 * Real.log 2) := by
  let f (n : ℕ) : ℝ := 1 / (((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) - 1))
  let a (n : ℕ) : ℝ := (-1 : ℝ) ^ n / ((n : ℝ) + 1)
  have hsum : Summable f := by
    have hp : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2
          (Real.summable_one_div_nat_pow.2 (by decide : 1 < (2 : ℕ)))
    refine Summable.of_nonneg_of_le ?_ ?_ hp
    · intro n
      dsimp [f]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      exact div_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith))
    · intro n
      dsimp [f]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      apply one_div_le_one_div_of_le (by positivity)
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hpair (n : ℕ) : f n = 2 * (a (2 * n) + a (2 * n + 1)) := by
    have he : (-1 : ℝ) ^ (2 * n) = 1 := (even_two_mul n).neg_one_pow
    simp only [f, a, pow_succ (-1 : ℝ) (2 * n), he, one_mul, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [show 2 * ((n : ℝ) + 1) - 1 = 2 * (n : ℝ) + 1 by ring]
    field_simp (disch := positivity)
    ring
  -- Only finite partial sums of the original alternating series are grouped.
  have hpartial (N : ℕ) : ∑ n ∈ Finset.range N, f n = 2 * ∑ n ∈ Finset.range (2 * N), a n := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega, Finset.sum_range_succ, ih, hpair N,
        Finset.sum_range_succ, Finset.sum_range_succ]
      ring
  have hdouble : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun N => by
      change N ≤ 2 * N
      omega) tendsto_id
  have hlim : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n) atTop (𝓝 (2 * Real.log 2)) := by
    simpa only [hpartial, Function.comp_apply, a] using
      (Real.tendsto_sum_alternating_harmonic.comp hdouble).const_mul 2
  have heq := tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim
  exact heq ▸ hsum.hasSum

private theorem hasSum_one_div_nat_add_one_pow {k : ℕ} (hk : 1 < k) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ k) (riemannZeta (k : ℂ)) := by
  have hre : 1 < (k : ℂ).re := by exact_mod_cast hk
  have hs := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ (k : ℂ)) 1).2
    (Complex.summable_one_div_nat_cpow.2 hre)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  simpa only [Nat.cast_add, Nat.cast_one, Complex.cpow_natCast] using hs.hasSum

private theorem inv_pow_mul_two_mul_sub_one_succ (t n : ℕ) :
    1 / (((n : ℂ) + 1) ^ (t + 1) * (2 * ((n : ℂ) + 1) - 1)) =
      2 * (1 / (((n : ℂ) + 1) ^ t * (2 * ((n : ℂ) + 1) - 1))) - 1 / ((n : ℂ) + 1) ^ (t + 1) := by
  have h (x : ℝ) (hx : 1 ≤ x) :
      1 / (x ^ (t + 1) * (2 * x - 1)) = 2 * (1 / (x ^ t * (2 * x - 1))) - 1 / x ^ (t + 1) := by
    have hx₀ : x ≠ 0 := by linarith
    have hodd : 2 * x - 1 ≠ 0 := by linarith
    generalize hy : 2 * x - 1 = y at hodd ⊢
    rw [pow_succ]
    field_simp [hx₀, hodd]
    rw [← hy]
    ring
  have hc := congrArg Complex.ofReal (h ((n : ℝ) + 1) (by simp))
  push_cast at hc
  exact hc

private theorem hasSum_inv_pow_mul_two_mul_sub_one (k : ℕ) :
    HasSum (fun n : ℕ => 1 / (((n : ℂ) + 1) ^ (k + 1) * (2 * ((n : ℂ) + 1) - 1)))
      (2 ^ (k + 1) * Real.log 2 -
        ∑ j ∈ Finset.Icc 1 k, (2 : ℂ) ^ (k - j) * riemannZeta ((j : ℂ) + 1)) := by
  induction k with
  | zero =>
    have h := Complex.hasSum_ofReal.mpr hasSum_inv_mul_two_mul_sub_one
    simpa [Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1)] using h
  | succ k ih =>
    have hz := hasSum_one_div_nat_add_one_pow (k := (k + 1) + 1) (by omega)
    have hstep := ((ih.mul_left 2).sub hz).congr_fun
      (fun n => inv_pow_mul_two_mul_sub_one_succ (k + 1) n)
    convert hstep using 1
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    simp only [Nat.sub_self, pow_zero, one_mul, Nat.cast_add, Nat.cast_one]
    have hsum : (∑ j ∈ Finset.Icc 1 k, (2 : ℂ) ^ (k + 1 - j) * riemannZeta ((j : ℂ) + 1)) =
        2 * ∑ j ∈ Finset.Icc 1 k, (2 : ℂ) ^ (k - j) * riemannZeta ((j : ℂ) + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjle := (Finset.mem_Icc.mp hj).2
      rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]
      ring
    rw [hsum, pow_succ]
    ring

/-- **Closed form of $\sum_{n \ge 1} 1/(n^t(2n-1))$.** For every integer $t \ge 1$,
$$\sum_{n \ge 1} \frac{1}{n^t (2n-1)} = 2^t \log 2 - \sum_{j=1}^{t-1} 2^{t-1-j} \zeta(j+1),$$
where $\zeta$ is the Riemann zeta function.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Corollary 1,
equation (22). -/
public theorem tsum_inv_pow_mul_two_mul_sub_one (t : ℕ) (ht : 0 < t) :
    ((∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ t * (2 * ((n : ℝ) + 1) - 1)) : ℝ) : ℂ) =
      2 ^ t * Real.log 2 -
        ∑ j ∈ Finset.Icc 1 (t - 1), (2 : ℂ) ^ (t - 1 - j) * riemannZeta ((j : ℂ) + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  simpa only [Complex.ofReal_tsum, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one, Complex.ofReal_ofNat, Nat.succ_sub_one] using
    (hasSum_inv_pow_mul_two_mul_sub_one k).tsum_eq

end MetaMathlibExt
