/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.RootsOfUnity.Complex
import MathlibExt.Quantum.RootsFilter

/-!
# Multisection of the linearly weighted reciprocal central binomial series

Summing over rotations of a principal `m`-th root selects positive multiples of `m`.
The resulting factor of `m` cancels against the linear weight in the denominator.
-/

namespace MetaMathlibExt

private theorem summable_norm_pow_div_mul_centralBinom {z : ℂ} (hz : ‖z‖ < 4) :
    Summable fun n : ℕ => ‖z ^ n / ((n : ℂ) * Nat.centralBinom n)‖ := by
  have hr : ‖‖z‖ / 4‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    linarith
  apply (summable_geometric_of_norm_lt_one hr).of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn
  have hbound : (4 : ℝ) ^ n ≤ n * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast (Nat.four_pow_lt_mul_centralBinom n hn).le
  rw [Real.norm_of_nonneg (norm_nonneg _), norm_div, norm_pow, norm_mul, Complex.norm_natCast,
    Complex.norm_natCast, div_pow]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hbound

/-- **Multisection formula for $\sum_k x^k / (k \binom{2mk}{mk})$.** Let $m \ge 1$ be a natural
number and $x$ a complex number with $|x| < 4^m$. Write
$L(y) = \sum_{n \ge 1} y^n / (n \binom{2n}{n})$, $w = e^{2\pi i/m}$, and let $x^{1/m}$ be the
principal $m$-th root of $x$. Then
$$
\sum_{k \ge 1} \frac{x^k}{k \binom{2mk}{mk}} = \sum_{j=0}^{m-1} L(w^j x^{1/m}).
$$

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Theorem 8 (`jis-2024-24.6.8-thm-8`). -/
public theorem tsum_div_mul_centralBinom_mul_eq_multisection {m : ℕ} (hm : 1 ≤ m)
    {x : ℂ} (hx : ‖x‖ < 4 ^ m) :
    ∑' k : ℕ, x ^ (k + 1) / (((k + 1 : ℕ) : ℂ) * Nat.centralBinom (m * (k + 1))) =
      ∑ j ∈ Finset.range m,
        ∑' n : ℕ, (Complex.exp (2 * Real.pi * Complex.I / m) ^ j * x ^ ((1 : ℂ) / m)) ^ (n + 1) /
          (((n + 1 : ℕ) : ℂ) * Nat.centralBinom (n + 1)) := by
  have hm0 : m ≠ 0 := by omega
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  let w := Complex.exp (2 * Real.pi * Complex.I / m)
  let z := x ^ ((1 : ℂ) / m)
  have hw : IsPrimitiveRoot w m := Complex.isPrimitiveRoot_exp m hm0
  have hz : z ^ m = x := by simpa [z, one_div] using Complex.cpow_nat_inv_pow x hm0
  have hzlt : ‖z‖ < 4 := lt_of_pow_lt_pow_left₀ m (by norm_num) (by rwa [← norm_pow, hz])
  have hs (j : ℕ) (_ : j ∈ Finset.range m) :
      Summable fun n : ℕ => (w ^ j * z) ^ (n + 1) /
        (((n + 1 : ℕ) : ℂ) * Nat.centralBinom (n + 1)) := by
    have hnorm : ‖w ^ j * z‖ < 4 := by
      simpa [norm_mul, norm_pow, hw.norm'_eq_one hm0] using hzlt
    exact (summable_nat_add_iff 1).2 (summable_norm_pow_div_mul_centralBinom hnorm).of_norm
  let f (n : ℕ) : ℂ := if m ∣ n + 1 then
    (m : ℂ) * (z ^ (n + 1) / (((n + 1 : ℕ) : ℂ) * Nat.centralBinom (n + 1))) else 0
  -- The finite sum of rotations selects precisely the positive indices divisible by m.
  have hfilter (n : ℕ) :
      (∑ j ∈ Finset.range m, (w ^ j * z) ^ (n + 1) /
        (((n + 1 : ℕ) : ℂ) * Nat.centralBinom (n + 1))) = f n := by
    simp_rw [mul_pow, pow_right_comm w _ (n + 1), mul_div_assoc]
    rw [← Finset.sum_mul, MathlibExt.Quantum.RootsFilter.roots_filter w hm hw.pow_eq_one]
    simp only [hw.pow_eq_one_iff_dvd, f]
    split <;> simp
  -- In the shifted indexing, k represents the positive multiple m * (k + 1).
  let g (k : ℕ) := m * (k + 1) - 1
  have hg_succ (k : ℕ) : g k + 1 = m * (k + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos hm (Nat.succ_pos k))
  have hg : Function.Injective g := by
    intro a b h
    apply Nat.succ.inj
    apply mul_right_injective₀ hm0
    exact (hg_succ a).symm.trans ((congrArg (· + 1) h).trans (hg_succ b))
  have hsupport : Function.support f ⊆ Set.range g := by
    intro n hn
    have hd : m ∣ n + 1 := by
      by_contra h
      exact hn (by simp [f, h])
    obtain ⟨k, hk⟩ := hd
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    exact ⟨k, Nat.succ.inj ((hg_succ k).trans hk.symm)⟩
  rw [← Summable.tsum_finsetSum hs]
  simp_rw [hfilter]
  rw [← hg.tsum_eq hsupport]
  refine tsum_congr fun k => ?_
  -- Cancel the filter's factor of m against the linear weight at the selected index.
  simp only [f, hg_succ, dvd_mul_right, ite_true, pow_mul, hz, Nat.cast_mul]
  rw [mul_assoc, ← mul_div_assoc, mul_div_mul_left _ _ hmC]

end MetaMathlibExt
