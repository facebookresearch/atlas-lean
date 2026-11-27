/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import MathlibExt.NumberTheory.TrinomialCoefficient
import all MathlibExt.Combinatorics.Enumerative.TrinomialEvenGenerating
import Mathlib.Tactic.Ring

/-!
# Odd-index trinomial coefficients

Subtracting the values of a trinomial row polynomial at opposite arguments cancels the even powers.

## References

* Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer
  Sequences 28 (2025), Article 25.3.5, Corollary 15 (p. 12).
* Otmani's coefficient-extraction proof uses his Eq. (13), which in turn uses Renzo Sprugnoli,
  *Riordan arrays and combinatorial sums*, Discrete Mathematics 132 (1994), 267–290,
  Theorem 1.1, and the coefficient scaling rule in Sprugnoli's
  *Riordan Array Proofs of Identities in Gould’s Book*, University of Florence (2006), p. 7,
  (0TR). The proof here instead evaluates the row polynomial directly.
-/

namespace MetaMathlibExt

private theorem sum_range_pairs {A : Type*} [AddCommMonoid A] (f : ℕ → A) (m : ℕ) :
    ∑ j ∈ Finset.range (2 * m), f j =
      ∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ, add_assoc]

/-- **Generating polynomial of trinomial coefficients with odd index.** Write $\binom{n}{k}_2$
for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. For every
$n \in \mathbb{N}$ and all complex numbers $z$ and $s$ with $s^2 = z$ and $s \ne 0$
$$\sum_{k=0}^{n} \binom{n}{2k+1}_2 z^k = \frac{(1 + s + z)^n - (1 - s + z)^n}{2s}.$$

The paper states this for an indeterminate $z$, with $\sqrt{z}$ in place of $s$, and calls the
left side $q_n(z)$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 15 (`jis-2025-25.3.5-cor-15`). -/
public theorem sum_trinomialCoefficient_odd (n : ℕ) (z s : ℂ) (hs : s ^ 2 = z)
    (hs0 : s ≠ 0) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient n (2 * k + 1) : ℂ) * z ^ k =
      ((1 + s + z) ^ n - (1 - s + z) ^ n) / (2 * s) := by
  let f (j : ℕ) := (trinomialCoefficient n j : ℂ) * s ^ j -
    (trinomialCoefficient n j : ℂ) * (-s) ^ j
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  apply (eq_div_iff (mul_ne_zero htwo hs0)).2
  calc
    _ = ∑ k ∈ Finset.range (n + 1), (f (2 * k) + f (2 * k + 1)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only [f]
      rw [pow_succ s (2 * k), pow_succ (-s) (2 * k), pow_mul s 2 k, pow_mul (-s) 2 k,
        neg_sq, hs]
      ring
    _ = ∑ j ∈ Finset.range (2 * (n + 1)), f j := (sum_range_pairs f (n + 1)).symm
    _ = _ := by
      simp only [f, Finset.sum_sub_distrib]
      rw [← eval_trinomial_row n s, ← eval_trinomial_row n (-s), neg_sq, hs, sub_eq_add_neg 1 s]

end MetaMathlibExt
