/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.NumberTheory.BernoulliFibonacciExpansion
public import MathlibExt.NumberTheory.GenocchiNumber
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Data.Nat.Choose.Cast
import MathlibExt.NumberTheory.ChurchBicknellFibonacciConvolution

/-!
# A vanishing sum of Genocchi–Lucas coefficients

Binet's formula and the Genocchi generating function give the corrected coefficient
`genLucasCoeff n = 2 * √5 * fibBeta ^ n`. The binomial theorem then gives the vanishing
sum at every positive exponent.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

open MetaMathlibExt

/-- **Genocchi–Lucas coefficients.** For a natural number $n$, the Genocchi–Lucas coefficient is
the real number
$$
c_n = \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k} G_k \frac{L_{n-k+1}}{n-k+1} +
2 \sqrt{5}^{\,n+1} \frac{G_{n+1}}{n+1},
$$
where $G_k$ are the Genocchi numbers and $L_k$ the Lucas numbers.

These are the inner coefficients of the corrected Theorem 11 of Bensaci, Boumahdi and Khaldi,
"Finite Sums Involving Fibonacci and Lucas Numbers"; the paper's printed coefficient omits the
last term. -/
noncomputable def genLucasCoeff (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), (Real.sqrt 5) ^ k *
      (Nat.choose n k : ℝ) * (genocchiNumber k : ℝ) *
      ((lucasNumber (n - k + 1) : ℝ) / (n - k + 1 : ℕ))) +
    2 * (Real.sqrt 5) ^ (n + 1) *
      ((genocchiNumber (n + 1) : ℝ) / (n + 1 : ℕ))

open PowerSeries Finset
open scoped goldenRatio

private noncomputable abbrev scaledGenocchi : PowerSeries ℝ :=
  rescale (Real.sqrt 5) (map (algebraMap ℚ ℝ) genocchiPowerSeries)

private noncomputable abbrev expAt (a : ℝ) := rescale a (exp ℝ)

private theorem coeff_scaledGenocchi (k : ℕ) :
    coeff k scaledGenocchi = (Real.sqrt 5) ^ k * (genocchiNumber k : ℝ) / k.factorial := by
  simp [scaledGenocchi, genocchiNumber, field]

private theorem coeff_lucasSeries (j : ℕ) :
    coeff j (expAt φ + expAt ψ) = (lucasNumber j : ℝ) / j.factorial := by
  simp [expAt, ← cb_lucas_binet, field]

-- Multiplication by the Lucas series cancels the denominator of the Genocchi series.
private theorem scaledGenocchi_mul_lucasSeries :
    scaledGenocchi * (expAt φ + expAt ψ) = (C (2 * Real.sqrt 5) * expAt ψ) * X := by
  have hG : genocchiPowerSeries * (exp ℚ + 1) = 2 * X := by
    rw [genocchiPowerSeries_eq, mul_assoc, PowerSeries.inv_mul_cancel]
    · simp
    · norm_num
  have hs : scaledGenocchi * (expAt (Real.sqrt 5) + 1) = 2 * (C (Real.sqrt 5) * X) := by
    simpa [scaledGenocchi, expAt, map_ofNat] using
      congrArg (fun f => rescale (Real.sqrt 5) (map (algebraMap ℚ ℝ) f)) hG
  have he : expAt (Real.sqrt 5) * expAt ψ = expAt φ := by
    rw [expAt, expAt, exp_mul_exp_eq_exp_add, ← Real.goldenRatio_sub_goldenConj, sub_add_cancel]
  rw [← he, ← add_one_mul, ← mul_assoc, hs, map_mul, map_ofNat]
  ring

private theorem genLucasCoeff_eq (n : ℕ) :
    genLucasCoeff n = 2 * Real.sqrt 5 * fibBeta ^ n := by
  calc
    genLucasCoeff n = (n.factorial : ℝ) *
        coeff (n + 1) (scaledGenocchi * (expAt φ + expAt ψ)) := by
      rw [genLucasCoeff, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        sum_range_succ _ (n + 1), mul_add, mul_sum]
      -- The final summand involves the initial Lucas number and gives the correction term.
      congr 1
      · refine sum_congr rfl fun k hk => ?_
        have hkn := mem_range_succ_iff.mp hk
        rw [coeff_scaledGenocchi, coeff_lucasSeries, Nat.cast_choose ℝ hkn,
          show n + 1 - k = n - k + 1 by omega, Nat.factorial_succ]
        simp [field]
      · rw [coeff_scaledGenocchi, coeff_lucasSeries, Nat.sub_self]
        simp [lucasNumber, Nat.factorial_succ, field]
    _ = 2 * Real.sqrt 5 * fibBeta ^ n := by
      rw [scaledGenocchi_mul_lucasSeries, coeff_succ_mul_X, coeff_C_mul]
      simp [expAt, fibBeta, field]

/-- **A vanishing sum of the corrected Genocchi–Lucas coefficients.** Let
$\beta = (1 - \sqrt{5})/2$, let $G_k$ be the Genocchi numbers and $L_n$ the Lucas numbers, and for
each natural number $n$ let
$$c_n = \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k} G_k \frac{L_{n-k+1}}{n-k+1} +
2\sqrt{5}^{\,n+1} \frac{G_{n+1}}{n+1}.$$
For every natural number $m \ge 1$, $\sum_{n=0}^{m} \binom{m}{n} c_n (-\beta)^{m-n} = 0$.

This is the case $x = -\beta$ of the corrected Theorem 11. As printed, with $\beta^{m-n}$ in place
of $(-\beta)^{m-n}$ and without the last term of $c_n$, the sum at $m = 2$ is $-10 + 4\sqrt{5}$.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 12. -/
theorem sum_genLucasCoeff_neg_fibBeta (m : ℕ)
    (hm : 1 ≤ m) :
    ∑ n ∈ Finset.range (m + 1),
        (Nat.choose m n : ℝ) * genLucasCoeff n *
          (-fibBeta) ^ (m - n) = 0 := by
  calc
    _ = 2 * Real.sqrt 5 * (fibBeta + -fibBeta) ^ m := by
      rw [add_pow, mul_sum]
      refine sum_congr rfl fun n _ => ?_
      rw [genLucasCoeff_eq]
      ring
    _ = 0 := by simp [zero_pow (by omega : m ≠ 0)]

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted
