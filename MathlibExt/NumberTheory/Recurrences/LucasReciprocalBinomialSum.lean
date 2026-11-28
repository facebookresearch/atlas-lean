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
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.LucasSequenceAddition

/-!
# Alternating reciprocal-binomial sum with Lucas sequences

For every integer $p$ and natural number $n$, the rational weights
$(-1)^k\binom{2n}{k}/(\binom{4n}{k}\binom{4n}{2n+k})$ for $0 \le k \le 2n$ are symmetric
under $k \mapsto 2n-k$. Their weighted sum of $U_k(p,-1)V_{2n-k}(p,-1)$ is
$\frac{4n+1}{(3n+1)\binom{4n}{2n}}\,U_{2n}(p,-1)$. Averaging the sum with its reflection
and using the Lucas addition formula reduces the identity to a scalar sum. After cancellation of
factorials in the weights, that sum telescopes.

## References

* John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
  Sequences*, The Fibonacci Quarterly 62 (2024), no. 1, 57–64, Proposition 2.9.
* Vladimir V. Kruchinin and Maria Y. Perminova, *Identities and Hadamard Product of the Generalized
  Fibonacci, Lucas, Catalan, and Harmonic Numbers*, Journal of Integer Sequences 28 (2025),
  Article 25.8.8, 1–17, Proposition 1 (Lucas addition) and Theorem 2 (symmetric weights).
* The reflection argument is analogous to `lucasU_lucasV_sum_choose_cube_alternating` in
  `MathlibExt.NumberTheory.Recurrences.LucasDixonBinomialSum`.
-/

namespace MetaMathlibExt

open Finset
open MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted (two_mul_lucasU_add)

private theorem reciprocal_weight_eq_factorials (n k : ℕ) (hk : k ≤ 2 * n) :
    ((2 * n).choose k : ℚ) / ((4 * n).choose k * (4 * n).choose (2 * n + k)) =
      ((2 * n).factorial : ℚ) / ((4 * n).factorial : ℚ) ^ 2 *
        ((2 * n + k).factorial * (4 * n - k).factorial) := by
  rw [Nat.cast_choose ℚ hk, Nat.cast_choose ℚ (show k ≤ 4 * n by omega),
    Nat.cast_choose ℚ (show 2 * n + k ≤ 4 * n by omega),
    show 4 * n - (2 * n + k) = 2 * n - k by omega]
  field_simp

private theorem sum_signed_factorials (n : ℕ) :
    ∑ k ∈ range (2 * n + 1), (-1 : ℚ) ^ k * (2 * n + k).factorial * (4 * n - k).factorial =
      ((2 * n).factorial : ℚ) * (4 * n + 1).factorial / (3 * (n : ℚ) + 1) := by
  let F (k : ℕ) : ℚ := (-1) ^ k * (2 * n + k).factorial * (4 * n + 1 - k).factorial
  have hstep (k : ℕ) (hk : k ≤ 2 * n) :
      (2 * (3 * (n : ℚ) + 1)) * ((-1 : ℚ) ^ k * (2 * n + k).factorial * (4 * n - k).factorial) =
        F k - F (k + 1) := by
    dsimp only [F]
    rw [show 4 * n + 1 - k = (4 * n - k) + 1 by omega,
      show 4 * n + 1 - (k + 1) = 4 * n - k by omega,
      ← Nat.add_assoc (2 * n) k 1, pow_succ,
      Nat.factorial_succ (4 * n - k), Nat.factorial_succ (2 * n + k)]
    push_cast [Nat.cast_sub (show k ≤ 4 * n by omega)]
    ring
  have hend : F 0 - F (2 * n + 1) = 2 * ((2 * n).factorial : ℚ) * (4 * n + 1).factorial := by
    simp only [F, pow_zero, Nat.add_zero, Nat.sub_zero, one_mul,
      show 2 * n + (2 * n + 1) = 4 * n + 1 by omega,
      show 4 * n + 1 - (2 * n + 1) = 2 * n by omega,
      pow_succ (-1 : ℚ) (2 * n), pow_mul, neg_one_sq, one_pow]
    ring
  have hsum := sum_congr (s₁ := range (2 * n + 1)) rfl
    (fun k hk => hstep k (mem_range_succ_iff.mp hk))
  rw [← mul_sum, sum_range_sub', hend] at hsum
  apply (eq_div_iff (by positivity)).2
  linear_combination hsum / 2

set_option backward.proofsInPublic true in
/-- **Alternating sum with reciprocal binomial coefficients and Lucas sequences.** Let $p$ be an
integer and let $U_n$ and $V_n$ be the Lucas sequences $U(p, -1)$ and $V(p, -1)$, so $U_0 = 0$,
$U_1 = 1$, $V_0 = 2$, $V_1 = p$ and both satisfy $X_{j+2} = p X_{j+1} + X_j$. Then for every
natural number $n$, in the rationals,
$$\sum_{k=0}^{2n} (-1)^k \frac{\binom{2n}{k}}{\binom{4n}{k} \binom{4n}{2n+k}} U_k V_{2n-k} =
\frac{4n+1}{3n+1} \cdot \frac{1}{\binom{4n}{2n}} U_{2n}.$$

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 2.9. -/
public theorem lucasU_lucasV_sum_choose_inv_alternating (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1),
        ((2 * n).choose k : ℚ) / ((4 * n).choose k * (4 * n).choose (2 * n + k)) * (-1) ^ k *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (2 * n - k) =
      (4 * n + 1 : ℚ) / (3 * n + 1) / (4 * n).choose (2 * n) * lucasU ⟨p, -1, by decide⟩ (2 * n)
    := by
  let P : LucasSequenceParams := ⟨p, -1, by decide⟩
  let u (j : ℕ) : ℚ := lucasU P j
  let v (j : ℕ) : ℚ := lucasV P j
  let a (k : ℕ) : ℚ :=
    ((2 * n).choose k : ℚ) / ((4 * n).choose k * (4 * n).choose (2 * n + k)) * (-1) ^ k
  have hsymm (k : ℕ) (hk : k ≤ 2 * n) : a (2 * n - k) = a k := by
    have hsign : (-1 : ℚ) ^ (2 * n - k) = (-1) ^ k := by
      rw [neg_one_pow_eq_pow_mod_two (2 * n - k), neg_one_pow_eq_pow_mod_two k,
        show (2 * n - k) % 2 = k % 2 by omega]
    dsimp only [a]
    rw [reciprocal_weight_eq_factorials n k hk,
      reciprocal_weight_eq_factorials n (2 * n - k) (by omega), hsign,
      show 2 * n + (2 * n - k) = 4 * n - k by omega,
      show 4 * n - (2 * n - k) = 2 * n + k by omega, mul_comm ((4 * n - k).factorial : ℚ)]
  have hrefl :
      ∑ k ∈ range (2 * n + 1), a k * u (2 * n - k) * v k =
        ∑ k ∈ range (2 * n + 1), a k * u k * v (2 * n - k) := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun k hk => ?_
    have hkn := mem_range_succ_iff.mp hk
    rw [Nat.add_sub_cancel, Nat.sub_sub_self hkn, hsymm k hkn]
  have hscalar :
      ∑ k ∈ range (2 * n + 1), a k = (4 * n + 1 : ℚ) / (3 * n + 1) / (4 * n).choose (2 * n) := by
    calc
      _ = ∑ k ∈ range (2 * n + 1), (((2 * n).factorial : ℚ) / ((4 * n).factorial : ℚ) ^ 2) *
          ((-1 : ℚ) ^ k * (2 * n + k).factorial * (4 * n - k).factorial) := by
        refine sum_congr rfl fun k hk => ?_
        dsimp only [a]
        rw [reciprocal_weight_eq_factorials n k (mem_range_succ_iff.mp hk)]
        ac_rfl
      _ = _ := by
        rw [← mul_sum, sum_signed_factorials, Nat.cast_choose ℚ (show 2 * n ≤ 4 * n by omega),
          show 4 * n - 2 * n = 2 * n by omega, Nat.factorial_succ (4 * n)]
        push_cast
        field_simp
  change (∑ k ∈ range (2 * n + 1), a k * u k * v (2 * n - k)) = _ * u (2 * n)
  calc
    _ = (∑ k ∈ range (2 * n + 1),
        (a k * u k * v (2 * n - k) + a k * u (2 * n - k) * v k)) / 2 := by
      rw [sum_add_distrib, hrefl]
      ring
    _ = (∑ k ∈ range (2 * n + 1), a k * (2 * u (2 * n))) / 2 := by
      congr 1
      refine sum_congr rfl fun k hk => ?_
      have hkn := mem_range_succ_iff.mp hk
      have h := two_mul_lucasU_add P k (2 * n - k)
      rw [show k + (2 * n - k) = 2 * n by omega, mul_comm (lucasV P k)] at h
      have hadd : u k * v (2 * n - k) + u (2 * n - k) * v k = 2 * u (2 * n) := by
        dsimp only [u, v]
        exact_mod_cast h.symm
      rw [← hadd, mul_add, mul_assoc (a k), mul_assoc (a k)]
    _ = _ := by rw [← sum_mul, hscalar]; ring

end MetaMathlibExt
