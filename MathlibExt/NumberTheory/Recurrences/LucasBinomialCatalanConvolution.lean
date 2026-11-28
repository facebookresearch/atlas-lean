/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import MathlibExt.NumberTheory.Recurrences.LucasAlternatingSquaredBinomialSum

/-!
# Binomial-Catalan convolution with Lucas sequences

For every integer $p$ and natural number $n$, the convolution of $U_{n-k}(p,-1)V_k(p,-1)$
with weights $\binom{2n}{2k} C_k C_{n-k}$ over $0 \le k \le n$ is $C_n C_{n+1} U_n(p,-1)$,
where $C_j$ is the $j$-th Catalan number. The weights are symmetric, so the Lucas factors
reduce to $U_n(p,-1)$ times the sum of the weights. The factorial formulas convert that
sum to Vandermonde's identity with upper indices $n$ and $n+2$.

## References

* John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
  Sequences*, The Fibonacci Quarterly 62 (2024), no. 1, 57–64, Proposition 2.11.
* Wenchang Chu and Emrah Kılıç, *Binomial sums involving Catalan numbers*, Rocky Mountain Journal
  of Mathematics 51 (2021), no. 4, 1221–1225, Theorem 1 (the scalar convolution cited in
  Proposition 2.11).
* Vladimir V. Kruchinin and Maria Y. Perminova, *Identities and Hadamard Product of the Generalized
  Fibonacci, Lucas, Catalan, and Harmonic Numbers*, Journal of Integer Sequences 28 (2025),
  Article 25.8.8, 1–17, Proposition 1 (Lucas addition) and Theorem 2 (symmetric weights).
* The formal proof uses `sum_mul_lucasU_mul_lucasV_of_symm` from
  `MathlibExt.NumberTheory.Recurrences.LucasAlternatingSquaredBinomialSum`.
-/

namespace MetaMathlibExt

open Finset
open lucasU_lucasV_sum_choose_sq_alternating (sum_mul_lucasU_mul_lucasV_of_symm)

private theorem cast_catalan_factorial (n : ℕ) :
    (catalan n : ℚ) = ((2 * n).factorial : ℚ) / (n.factorial * (n + 1).factorial) := by
  have h : (catalan n : ℚ) * ((n + 1 : ℕ) : ℚ) = n.centralBinom := by
    exact_mod_cast (mul_comm (catalan n) (n + 1)).trans (succ_mul_catalan_eq_centralBinom n)
  rw [Nat.centralBinom, Nat.cast_choose ℚ (show n ≤ 2 * n by omega),
    show 2 * n - n = n by omega] at h
  rw [Nat.factorial_succ, Nat.cast_mul, eq_div_iff_mul_eq (by positivity)]
  have hmul := (eq_div_iff_mul_eq (by positivity)).mp h
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul

private theorem sum_choose_mul_catalan (n : ℕ) :
    ∑ k ∈ range (n + 1), (2 * n).choose (2 * k) * catalan k * catalan (n - k) =
      catalan n * catalan (n + 1) := by
  have hchoose : ∑ k ∈ range (n + 1), n.choose k * (n + 2).choose (n + 1 - k) =
      (n + (n + 2)).choose (n + 1) := by
    symm
    rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ]
    simp
  suffices ∑ k ∈ range (n + 1), ((2 * n).choose (2 * k) : ℚ) * catalan k * catalan (n - k) =
      (catalan n : ℚ) * catalan (n + 1) by exact_mod_cast this
  let c : ℚ := ((2 * n).factorial : ℚ) / (n.factorial * (n + 2).factorial)
  have hchooseQ : ∑ k ∈ range (n + 1), (n.choose k : ℚ) * (n + 2).choose (n + 1 - k) =
      (n + (n + 2)).choose (n + 1) := by exact_mod_cast hchoose
  calc
    _ = ∑ k ∈ range (n + 1), c * ((n.choose k : ℚ) * (n + 2).choose (n + 1 - k)) := by
      refine sum_congr rfl fun k hk => ?_
      have hkn := mem_range_succ_iff.mp hk
      rw [Nat.cast_choose ℚ (show 2 * k ≤ 2 * n by omega), cast_catalan_factorial k,
        cast_catalan_factorial (n - k), Nat.cast_choose ℚ hkn,
        Nat.cast_choose ℚ (show n + 1 - k ≤ n + 2 by omega),
        ← Nat.mul_sub_left_distrib, show n + 1 - k = n - k + 1 by omega,
        show n + 2 - (n - k + 1) = k + 1 by omega]
      dsimp only [c]
      field_simp
    _ = c * ((n + (n + 2)).choose (n + 1) : ℚ) := by rw [← mul_sum, hchooseQ]
    _ = _ := by
      rw [cast_catalan_factorial n, cast_catalan_factorial (n + 1),
        Nat.cast_choose ℚ (show n + 1 ≤ n + (n + 2) by omega),
        show n + (n + 2) - (n + 1) = n + 1 by omega,
        show n + (n + 2) = 2 * (n + 1) by omega]
      dsimp only [c]
      field_simp

set_option backward.proofsInPublic true in
/-- **Binomial-Catalan sum with Lucas sequences.** Let $p$ be an integer, let $U_n$ and $V_n$ be
the Lucas sequences $U(p, -1)$ and $V(p, -1)$, so $U_0 = 0$, $U_1 = 1$, $V_0 = 2$, $V_1 = p$ and
both satisfy $X_{j+2} = p X_{j+1} + X_j$, and let $C_j$ be the $j$-th Catalan number. Then for
every natural number $n$,
$$\sum_{k=0}^{n} \binom{2n}{2k} C_k C_{n-k} U_{n-k} V_k = C_n C_{n+1} U_n.$$

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023,
Proposition 2.11. -/
public theorem lucasU_lucasV_sum_choose_catalan (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        ((2 * n).choose (2 * k) * catalan k * catalan (n - k) : ℤ) *
          lucasU ⟨p, -1, by decide⟩ (n - k) * lucasV ⟨p, -1, by decide⟩ k =
      (catalan n * catalan (n + 1) : ℤ) * lucasU ⟨p, -1, by decide⟩ n := by
  let a (k : ℕ) : ℤ := (2 * n).choose (2 * k) * catalan k * catalan (n - k)
  have ha (k : ℕ) (hk : k ≤ n) : a (n - k) = a k := by
    dsimp only [a]
    rw [Nat.sub_sub_self hk, Nat.mul_sub_left_distrib,
      Nat.choose_symm (show 2 * k ≤ 2 * n by omega)]
    ac_rfl
  have hsum : ∑ k ∈ range (n + 1), a k = (catalan n * catalan (n + 1) : ℤ) := by
    dsimp only [a]
    exact_mod_cast sum_choose_mul_catalan n
  rw [sum_mul_lucasU_mul_lucasV_of_symm _ n a ha, hsum]

end MetaMathlibExt
