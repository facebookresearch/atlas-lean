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
# Multisection of the reciprocal central binomial series

Averaging the series over the rotations of a principal `m`-th root selects the coefficients
whose indices are divisible by `m`.
-/

namespace MetaMathlibExt

private theorem summable_pow_div_centralBinom {z : ℂ} (hz : ‖z‖ < 4) :
    Summable fun n : ℕ => z ^ n / (Nat.centralBinom n : ℂ) := by
  have hr : ‖‖z‖ / 4‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    linarith
  have hs : Summable fun n : ℕ => (n : ℝ) * (‖z‖ / 4) ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn
  have hc : (0 : ℝ) < Nat.centralBinom n := by exact_mod_cast Nat.centralBinom_pos n
  have hbound : (4 : ℝ) ^ n ≤ n * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast (Nat.four_pow_lt_mul_centralBinom n hn).le
  rw [norm_div, norm_pow, Complex.norm_natCast, div_pow, ← mul_div_assoc,
    div_le_div_iff₀ hc (by positivity)]
  calc
    _ ≤ ‖z‖ ^ n * (n * (Nat.centralBinom n : ℝ)) := by gcongr
    _ = _ := by ring

/-- **Multisection formula for $\sum_k x^k / \binom{2mk}{mk}$.** Let $m \ge 1$ be a natural number
and $x$ a complex number with $|x| < 4^m$. Write $H(y) = \sum_{n \ge 0} y^n / \binom{2n}{n}$,
$w = e^{2\pi i/m}$, and let $x^{1/m}$ be the principal $m$-th root of $x$. Then
$$
\sum_{k \ge 0} \frac{x^k}{\binom{2mk}{mk}} = \frac{1}{m} \sum_{j=0}^{m-1} H(w^j x^{1/m}).
$$

Source: Rimer Zurita, *Elementary Functions Associated with Series Involving Reciprocals of
Central Binomial Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.6.8,
Theorem 7 (`jis-2024-24.6.8-thm-7`). -/
public theorem tsum_div_centralBinom_mul_eq_multisection {m : ℕ} (hm : 1 ≤ m) {x : ℂ}
    (hx : ‖x‖ < 4 ^ m) :
    ∑' k : ℕ, x ^ k / (Nat.centralBinom (m * k) : ℂ) =
      (1 / m : ℂ) * ∑ j ∈ Finset.range m,
        ∑' n : ℕ, (Complex.exp (2 * Real.pi * Complex.I / m) ^ j * x ^ ((1 : ℂ) / m)) ^ n /
          (Nat.centralBinom n : ℂ) := by
  have hm0 : m ≠ 0 := by omega
  let w := Complex.exp (2 * Real.pi * Complex.I / m)
  let z := x ^ ((1 : ℂ) / m)
  have hw : IsPrimitiveRoot w m := Complex.isPrimitiveRoot_exp m hm0
  have hz : z ^ m = x := by simpa [z, one_div] using Complex.cpow_nat_inv_pow x hm0
  have hzlt : ‖z‖ < 4 := lt_of_pow_lt_pow_left₀ m (by norm_num) (by rwa [← norm_pow, hz])
  have hs (j : ℕ) (_ : j ∈ Finset.range m) :
      Summable fun n : ℕ => (w ^ j * z) ^ n / (Nat.centralBinom n : ℂ) := by
    apply summable_pow_div_centralBinom
    simpa [norm_mul, norm_pow, hw.norm'_eq_one hm0] using hzlt
  -- The average of each coefficient vanishes unless its index is a multiple of m.
  have hfilter (n : ℕ) :
      (1 / m : ℂ) * ∑ j ∈ Finset.range m, (w ^ j * z) ^ n / (Nat.centralBinom n : ℂ) =
        if m ∣ n then z ^ n / (Nat.centralBinom n : ℂ) else 0 := by
    simp_rw [mul_pow, pow_right_comm w _ n, mul_div_assoc]
    rw [← Finset.sum_mul, MathlibExt.Quantum.RootsFilter.roots_filter w hm hw.pow_eq_one]
    simp only [hw.pow_eq_one_iff_dvd]
    split <;> simp [hm0]
  rw [← Summable.tsum_finsetSum hs, ← tsum_mul_left]
  simp_rw [hfilter]
  -- Reindex the surviving terms by k ↦ m * k.
  let f (n : ℕ) : ℂ := if m ∣ n then z ^ n / (Nat.centralBinom n : ℂ) else 0
  have hsupport : Function.support f ⊆ Set.range (m * ·) := by
    intro n hn
    by_contra h
    have hnd : ¬ m ∣ n := fun ⟨k, hk⟩ => h ⟨k, hk.symm⟩
    exact hn (by simp [f, hnd])
  simpa [f, pow_mul, hz] using (mul_right_injective₀ hm0).tsum_eq hsupport

end MetaMathlibExt
