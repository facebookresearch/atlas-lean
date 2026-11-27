/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Ring
public import MathlibExt.Algebra.Polynomial.ChebyshevCPartialSum

/-!
# Leading coefficients of the partial sums of monic Chebyshev polynomials

## References

* [C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*](https://cs.uwaterloo.ca/journals/JIS/VOL29/Kassel/kas20.pdf),
  Journal of Integer Sequences 29 (2026), Article 26.4.4, pp. 1–25,
  Proposition 9 and Corollary 10 (p. 12); see also Table 4 (p. 11).
* M. Abramowitz and I. A. Stegun (eds.), *Handbook of Mathematical Functions with Formulas,
  Graphs, and Mathematical Tables*, Dover (1972), p. 778, Eq. 22.5.11, for the monic
  normalization cited in §3.1 of Kassel and Reutenauer.
* A. F. Horadam, *Vieta polynomials*, Fibonacci Quarterly 40 (2002), 223–232,
  for the Vieta–Lucas terminology noted in §3.1 of Kassel and Reutenauer.
* T. J. Rivlin, *Chebyshev Polynomials*, 2nd ed., Wiley (1990), for the classical
  Chebyshev background cited in §3.1 of Kassel and Reutenauer.
-/

open Polynomial

namespace MetaMathlibExt

/-- **Leading coefficients of the partial sums of Chebyshev polynomials.** Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
For every $n \ge 5$, the polynomial
$$F_n - \Big(X^n + X^{n-1} - (n-1) X^{n-2} - (n-2) X^{n-3} + \binom{n-2}{2} X^{n-4} +
\binom{n-3}{2} X^{n-5}\Big)$$
is either zero or has degree less than $n - 5$.

Here $\binom{n-2}{2} = (n-2)(n-3)/2$ and $\binom{n-3}{2} = (n-3)(n-4)/2$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Corollary 10
(`jis-2026-26.4.4-cor-10`). -/
public theorem chebyshevCPartialSum_top_coeffs (n : ℕ) (hn : 5 ≤ n) :
    (chebyshevCPartialSum n -
        (X ^ n + X ^ (n - 1) - ((n - 1 : ℕ) : ℤ[X]) * X ^ (n - 2) -
          ((n - 2 : ℕ) : ℤ[X]) * X ^ (n - 3) + ((n - 2).choose 2 : ℤ[X]) * X ^ (n - 4) +
          ((n - 3).choose 2 : ℤ[X]) * X ^ (n - 5))).degree <
      ((n - 5 : ℕ) : WithBot ℕ) := by
  let term (d j : ℕ) : ℤ[X] := (-1) ^ j * ((d - j).choose j : ℤ[X]) * X ^ (d - 2 * j)
  have hsum : chebyshevCPartialSum n =
      (∑ j ∈ Finset.range (n / 2 + 1), term n j) +
        ∑ j ∈ Finset.range ((n - 1) / 2 + 1), term (n - 1) j := by
    simpa only [term, Nat.sub_right_comm n 1] using
      chebyshevCPartialSum_eq_binomial_sum n (by omega)
  have split (f : ℕ → ℤ[X]) (N : ℕ) (hN : 3 ≤ N) :
      (∑ j ∈ Finset.range N, f j) =
        f 0 + f 1 + f 2 + ∑ i ∈ Finset.range (N - 3), f (3 + i) := by
    conv_lhs => rw [show N = 3 + (N - 3) by omega, Finset.sum_range_add]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  -- Remove indices 0, 1 and 2 from each sum. The remaining ranges may be empty.
  have htail (d k : ℕ) (hd : d ≤ n) (hk : n - 5 ≤ k) :
      (∑ i ∈ Finset.range (d / 2 + 1 - 3), term d (3 + i)).coeff k = 0 := by
    rw [finsetSum_coeff]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hC : C ((-1 : ℤ) ^ (3 + i) * ((d - (3 + i)).choose (3 + i) : ℤ)) =
        (-1 : ℤ[X]) ^ (3 + i) * ((d - (3 + i)).choose (3 + i) : ℤ[X]) := by
      simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    have hdegree : d - 2 * (3 + i) < n - 5 := by omega
    simp only [term, ← hC, coeff_C_mul_X_pow, ite_eq_right (ne_of_gt (hdegree.trans_le hk))]
  rw [hsum, split (term n) _ (by omega), split (term (n - 1)) _ (by omega),
    degree_lt_iff_coeff_zero]
  intro k hk
  simp only [coeff_sub, coeff_add, htail n k le_rfl hk, htail (n - 1) k (by omega) hk, add_zero]
  simp only [term, pow_zero, pow_one, neg_one_sq, Nat.sub_zero, Nat.choose_zero_right,
    Nat.choose_one_right, Nat.cast_one, one_mul, neg_mul, Nat.reduceMul,
    show n - 1 - 1 = n - 2 by omega, show n - 1 - 2 = n - 3 by omega,
    show n - 1 - 4 = n - 5 by omega, mul_zero, coeff_neg]
  ring

end MetaMathlibExt
