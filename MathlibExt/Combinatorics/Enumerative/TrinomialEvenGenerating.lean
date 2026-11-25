/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import MathlibExt.NumberTheory.TrinomialCoefficient
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.Ring

/-!
# Even-index trinomial coefficients

Averaging the trinomial row polynomial at opposite arguments cancels the odd powers.
-/

namespace MetaMathlibExt

open Polynomial

private theorem eval_trinomial_row (n : ℕ) (t : ℂ) :
    (1 + t + t ^ 2) ^ n =
      ∑ j ∈ Finset.range (2 * (n + 1)), (trinomialCoefficient n j : ℂ) * t ^ j := by
  let p : ℕ[X] := 1 + X + X ^ 2
  have hp : p.natDegree ≤ 2 := by
    exact natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (by simp) (by simp)) (natDegree_X_pow_le 2)
  have hdeg : (p ^ n).natDegree < 2 * (n + 1) := by
    have h := natDegree_pow_le_of_le n hp
    omega
  calc
    _ = (p ^ n).eval₂ (Nat.castRingHom ℂ) t := by
      simp only [p, eval₂_pow, eval₂_add, eval₂_one, eval₂_X]
    _ = _ := eval₂_eq_sum_range' (Nat.castRingHom ℂ) hdeg t

/-- **Generating polynomial of trinomial coefficients with even index.** Write $\binom{n}{k}_2$
for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. For every
$n \in \mathbb{N}$ and all complex numbers $z$ and $s$ with $s^2 = z$
$$\sum_{k=0}^{n} \binom{n}{2k}_2 z^k = \frac{(1 + s + z)^n + (1 - s + z)^n}{2}.$$

The paper states this for an indeterminate $z$, with $\sqrt{z}$ in place of $s$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 13 (`jis-2025-25.3.5-cor-13`). -/
public theorem sum_trinomialCoefficient_even (n : ℕ) (z s : ℂ) (hs : s ^ 2 = z) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient n (2 * k) : ℂ) * z ^ k =
      ((1 + s + z) ^ n + (1 - s + z) ^ n) / 2 := by
  let f (j : ℕ) := (trinomialCoefficient n j : ℂ) * s ^ j +
    (trinomialCoefficient n j : ℂ) * (-s) ^ j
  -- Group consecutive terms of the sum into one even and one odd index.
  have hpair (m : ℕ) : ∑ j ∈ Finset.range (2 * m), f j =
      ∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1)) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ, add_assoc]
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  calc
    _ = ∑ k ∈ Finset.range (n + 1), (f (2 * k) + f (2 * k + 1)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only [f]
      rw [pow_succ s (2 * k), pow_succ (-s) (2 * k), pow_mul s 2 k, pow_mul (-s) 2 k,
        neg_sq, hs]
      ring
    _ = ∑ j ∈ Finset.range (2 * (n + 1)), f j := (hpair (n + 1)).symm
    _ = _ := by
      simp only [f, Finset.sum_add_distrib, ← eval_trinomial_row, neg_sq, hs, sub_eq_add_neg]

end MetaMathlibExt
