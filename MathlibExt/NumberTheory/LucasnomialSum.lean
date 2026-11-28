/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import MathlibExt.NumberTheory.LucasPolytopicNumber
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Sum formula for Lucasnomial coefficients

A first-order recurrence for Lucas brackets gives a weighted Pascal recurrence for
Lucasnomial coefficients. Iterating it along a column gives the sum formula.
-/

namespace MetaMathlibExt

namespace lucasnomial_succ_eq_sum_lucasPolytopic

variable (P : LucasParameters) {x y : ℝ} (hs : x + y = P.s) (ht : x * y = -P.t)

include hs ht

private theorem bracket_succ (n : ℕ) :
    lucasBracket P (n + 1) = x * lucasBracket P n + y ^ n := by
  induction n with
  | zero => simp [lucasBracket, lucasBracketAux]
  | succ n ih =>
    change P.s * lucasBracket P (n + 1) + P.t * lucasBracket P n = _
    rw [← hs, show P.t = -(x * y) by rw [ht, neg_neg], pow_succ]
    linear_combination y * ih

private theorem bracket_add (n m : ℕ) :
    lucasBracket P (n + m) = x ^ m * lucasBracket P n + y ^ n * lucasBracket P m := by
  induction m with
  | zero => simp [lucasBracket, lucasBracketAux]
  | succ m ih =>
    rw [← Nat.add_assoc, bracket_succ P hs ht (n + m), ih, bracket_succ P hs ht m,
      pow_succ, pow_add]
    ring

private theorem pascal (n d : ℕ) :
    lucasnomial P ((n + 1) + (d + 1)) (d + 1) =
      x ^ (d + 1) * lucasnomial P ((n + 1) + d) (d + 1) +
      y ^ (n + 1) * lucasnomial P ((n + 1) + d) d := by
  simp (disch := omega) only [lucasnomial, ite_eq_left, Nat.add_sub_cancel,
    show n + 1 + d - (d + 1) = n by omega]
  rw [← Nat.add_assoc, lucasFactorial_succ P (n + 1 + d),
    Nat.add_assoc (n + 1) d 1, bracket_add P hs ht (n + 1) (d + 1)]
  rw [lucasFactorial_succ P d, lucasFactorial_succ P n]
  field_simp [lucasFactorial_ne_zero, lucasBracket_ne_zero P (Nat.succ_ne_zero _)]

private theorem sum_formula (n d : ℕ) (hn : 1 ≤ n) :
    lucasnomial P (n + d) (d + 1) =
      ∑ k ∈ Finset.Icc 1 n, x ^ ((d + 1) * (n - k)) * y ^ (k - 1) *
        lucasnomial P (k + d - 1) d := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  clear hn
  induction m with
  | zero =>
    simp [Nat.add_comm 1 d, lucasnomial, lucasFactorial_ne_zero]
  | succ m ih =>
    rw [show (m + 1) + 1 + d = (m + 1) + (d + 1) by omega, pascal P hs ht m d,
      ih, Finset.mul_sum, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1 + 1)]
    simp only [Nat.sub_self, Nat.mul_zero, pow_zero, one_mul, Nat.add_sub_cancel,
      show m + 1 + 1 + d - 1 = m + 1 + d by omega]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := (Finset.mem_Icc.mp hk).2
    rw [show m + 1 + 1 - k = 1 + (m + 1 - k) by omega, Nat.mul_add, Nat.mul_one, pow_add]
    ring

end lucasnomial_succ_eq_sum_lucasPolytopic

open lucasnomial_succ_eq_sum_lucasPolytopic in
/-- **Sum formula for Lucasnomial coefficients.** Let $(s, t)$ be nondegenerate Lucas parameters,
with Lucasnomial coefficients $\binom{n}{k}_{s,t}$, and let $\varphi$ and $\varphi'$ be real
numbers with $\varphi + \varphi' = s$ and $\varphi \varphi' = -t$. For all natural numbers
$n \ge 1$ and $d$,
$$\binom{n+d}{d+1}_{s,t} = \sum_{k=1}^{n} \varphi^{(d+1)(n-k)} \varphi'^{k-1}
\binom{k+d-1}{d}_{s,t},$$
and the same holds with $\varphi$ and $\varphi'$ exchanged.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 2
(`jis-2025-25.5.6-thm-2`). -/
public theorem lucasnomial_succ_eq_sum_lucasPolytopic (P : LucasParameters) (φ φ' : ℝ)
    (hsum : φ + φ' = P.s) (hprod : φ * φ' = -P.t) (n d : ℕ) (hn : 1 ≤ n) :
    lucasnomial P (n + d) (d + 1) =
        ∑ k ∈ Finset.Icc 1 n, φ ^ ((d + 1) * (n - k)) * φ' ^ (k - 1) *
          lucasnomial P (k + d - 1) d ∧
      lucasnomial P (n + d) (d + 1) =
        ∑ k ∈ Finset.Icc 1 n, φ' ^ ((d + 1) * (n - k)) * φ ^ (k - 1) *
          lucasnomial P (k + d - 1) d := by
  exact ⟨sum_formula P hsum hprod n d hn,
    sum_formula P ((add_comm φ' φ).trans hsum) ((mul_comm φ' φ).trans hprod) n d hn⟩

end MetaMathlibExt
