/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Prime.Basic

/-!
# Bases of binomial forms of powers of two

Evaluating the scaled binomial coefficients as base-`b` digits gives `α * (b + 1) ^ k`.
For positive `k`, both `α` and `b + 1` divide this value. This argument works for any
`b` and `α`. The statement retains their lower bounds from the definition of binomial form.
-/

namespace MetaMathlibExt

set_option linter.unusedVariables false in
/-- **Bases of binomial forms of powers of 2.** Let $n$, $b \ge 2$, $\alpha \ge 1$ and $k \ge 1$
be natural numbers. If the base-$b$ digits of $2^n$, from the most significant to the least
significant, are $\alpha\binom{k}{k}, \alpha\binom{k}{k-1}, \dots, \alpha\binom{k}{0}$, then
$b = 2^x - 1$ for some natural number $x \le n$, and $\alpha = 2^i$ for some natural number $i$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Lemma 2
(`integers-2024-A69-lem-2`). -/
public theorem binomialForm_two_pow_base (n b α k : ℕ) (hb : 2 ≤ b) (hα : 1 ≤ α)
    (hk : 1 ≤ k) (h : Nat.digits b (2 ^ n) = (List.range (k + 1)).map fun i => α * k.choose i) :
    (∃ x ≤ n, b = 2 ^ x - 1) ∧ ∃ i, α = 2 ^ i := by
  have hpow : 2 ^ n = α * (b + 1) ^ k := calc
    2 ^ n = Nat.ofDigits b ((List.range (k + 1)).map fun i => α * k.choose i) := by
      rw [← h, Nat.ofDigits_digits]
    _ = ∑ i ∈ Finset.range (k + 1), α * k.choose i * b ^ i := by
      rw [Nat.ofDigits_eq_sum_mapIdx, Finset.sum_range, ← Fin.sum_ofFn]
      congr 1
      apply List.ext_getElem
      · simp only [List.length_mapIdx, List.length_map, List.length_range, List.length_ofFn]
      · intro i hi hj
        simp only [List.getElem_mapIdx, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    _ = α * (b + 1) ^ k := by
      simp [add_pow, Finset.mul_sum, mul_left_comm, mul_comm]
  have hbase : b + 1 ∣ 2 ^ n := by
    rw [hpow]
    exact (dvd_pow_self (b + 1) (Nat.ne_of_gt hk)).mul_left α
  have hscale : α ∣ 2 ^ n := ⟨_, hpow⟩
  obtain ⟨x, hxn, hx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hbase
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hscale
  exact ⟨⟨x, hxn, Nat.eq_sub_of_add_eq hx⟩, i, hi⟩

end MetaMathlibExt
