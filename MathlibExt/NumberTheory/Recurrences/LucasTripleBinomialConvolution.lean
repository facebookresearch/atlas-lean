/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import MathlibExt.NumberTheory.Recurrences.LucasAlternatingSquaredBinomialSum

/-!
# Lucas convolution with triple binomial weights

Choosing the same nested subsets in two ways reduces the triple weight to a central binomial
coefficient times a squared binomial coefficient. Reflecting the index then gives the
squared-binomial Lucas convolution, which uses the Lucas addition formula and
Vandermonde's identity.

## References

* John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
  Sequences*, The Fibonacci Quarterly 62 (2024), no. 1, 57–64, Propositions 2.3 and 2.10.
* Vladimir V. Kruchinin and Maria Y. Perminova, *Identities and Hadamard Product of the Generalized
  Fibonacci, Lucas, Catalan, and Harmonic Numbers*, Journal of Integer Sequences 28 (2025),
  Article 25.8.8, 1–17, Proposition 1 (Lucas addition formula) and Theorem 2 (symmetric weights).
-/

namespace MetaMathlibExt

open Finset

set_option backward.proofsInPublic true in
/-- **Sum of $\binom{n}{k} \binom{2n}{n+k} \binom{n+k}{k}$ with Lucas sequences.** Let $p$ be an
integer and let $U_n$ and $V_n$ be the Lucas sequences $U(p, -1)$ and $V(p, -1)$, so $U_0 = 0$,
$U_1 = 1$, $V_0 = 2$, $V_1 = p$ and both satisfy $X_{j+2} = p X_{j+1} + X_j$. Then for every
natural number $n$,
$$\sum_{k=0}^{n} \binom{n}{k} \binom{2n}{n+k} \binom{n+k}{k} U_k V_{n-k} = \binom{2n}{n}^2 U_n.$$

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 2.10. -/
public theorem lucasU_lucasV_sum_choose_n_plus_k (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (n.choose k * (2 * n).choose (n + k) * (n + k).choose k : ℤ) *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (n - k) =
      ((2 * n).choose n : ℤ) ^ 2 * lucasU ⟨p, -1, by decide⟩ n := by
  let P : LucasSequenceParams := ⟨p, -1, by decide⟩
  have hweight (k : ℕ) :
      (n.choose k * (2 * n).choose (n + k) * (n + k).choose k : ℤ) =
        ((2 * n).choose n : ℤ) * (n.choose k : ℤ) ^ 2 := by
    have hprod : (2 * n).choose (n + k) * (n + k).choose n = (2 * n).choose n * n.choose k := by
      simpa only [two_mul, Nat.add_sub_cancel_left] using
        (Nat.choose_mul (n := 2 * n) (Nat.le_add_right n k))
    norm_cast
    rw [← Nat.choose_symm_add (a := n) (b := k), mul_assoc, hprod, pow_two, mul_left_comm]
  have hsquared :
      ∑ k ∈ range (n + 1), (n.choose k : ℤ) ^ 2 * lucasU P k * lucasV P (n - k) =
        ((2 * n).choose n : ℤ) * lucasU P n := by
    rw [← sum_range_reflect]
    refine Eq.trans (sum_congr rfl fun k hk => ?_) (lucasU_lucasV_sum_choose_sq p n)
    have hkn := mem_range_succ_iff.mp hk
    rw [Nat.add_sub_cancel, Nat.sub_sub_self hkn, Nat.choose_symm hkn]
  change (∑ k ∈ range (n + 1),
    (n.choose k * (2 * n).choose (n + k) * (n + k).choose k : ℤ) *
      lucasU P k * lucasV P (n - k)) = ((2 * n).choose n : ℤ) ^ 2 * lucasU P n
  calc
    _ = ∑ k ∈ range (n + 1), ((2 * n).choose n : ℤ) *
          ((n.choose k : ℤ) ^ 2 * lucasU P k * lucasV P (n - k)) := by
      refine sum_congr rfl fun k _ => ?_
      rw [hweight]
      simp only [mul_assoc]
    _ = _ := by rw [← mul_sum, hsquared, pow_two, mul_assoc]

end MetaMathlibExt
