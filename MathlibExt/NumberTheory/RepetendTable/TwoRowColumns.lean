/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Matching columns of a two-row repetend table

For a modulus `n` and a length `L`, the rows of a repetend table are the bases `c` with
`1 ≤ c < n`, `gcd(c, n) = 1` and multiplicative order `L` modulo `n`, and column `k` is the
multiset of the digits `r_k(c) = ⌊c^(k+1)/n⌋ mod c` over the rows. When the table has exactly two
rows `b ≠ b'`, matching columns `i` and `j` have row differences `D_k = r_k(b') - r_k(b)` with
`D_i = ±D_j`, and they have the same sum (`MetaMathlibExt.repetend_digit_diff_of_columns_eq`;
its docstring gives the source).

## Proof outline

The rows are `b` and `b'`, so column `k` is the two-element multiset `{r_k(b), r_k(b')}`. If
columns `i` and `j` are equal, they have the same sum, and the digit `r_i(b)` lies in column `j`,
so it is `r_j(b)` or `r_j(b')`. In the first case the sums give `r_i(b') = r_j(b')`, hence
`D_i = D_j`; in the second they give `r_i(b') = r_j(b)`, hence `D_i = -D_j`.
-/

public section

namespace MetaMathlibExt

/-- **Matching columns of a two-row repetend table.** Let $n$ and $L$ be natural numbers and let
$B$ be the set of integers $c$ with $1 \le c < n$, $\gcd(c, n) = 1$ and multiplicative order $L$
modulo $n$. For $c \in B$ and $k \ge 0$ let $r_k(c) = \lfloor c^{k+1}/n \rfloor \bmod c$, and let
$C_k$ be the multiset of the $r_k(c)$ over $c \in B$. Suppose $B$ has exactly two elements, $b$
and $b' \ne b$, and put $D_k = r_k(b') - r_k(b)$. Then for all $i, j \ge 0$ with $C_i = C_j$,
$D_i = D_j$ or $D_i = -D_j$, and the sum of the elements of $C_i$ equals that of $C_j$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 28 (`integers-2025-A26-lem-28`). -/
theorem repetend_digit_diff_of_columns_eq (n L b b' i j : ℕ) :
    let B := (Finset.Ico 1 n).filter fun c => Nat.Coprime c n ∧ orderOf (c : ZMod n) = L
    let C : ℕ → Multiset ℕ := fun k => B.val.map fun c => c ^ (k + 1) / n % c
    let D : ℕ → ℤ := fun k => ((b' ^ (k + 1) / n % b' : ℕ) : ℤ) - (b ^ (k + 1) / n % b : ℕ)
    B.card = 2 → b ∈ B → b' ∈ B → b ≠ b' → C i = C j →
      (D i = D j ∨ D i = -D j) ∧ (C i).sum = (C j).sum := by
  intro B C D hcard hb hb' hne hC
  -- The two rows are `b` and `b'`.
  have hB : B = {b, b'} :=
    (Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hb (Finset.singleton_subset_iff.mpr hb'))
      (by rw [hcard, Finset.card_pair hne])).symm
  -- So column `k` is the pair of the digits of the two rows.
  have hCk (k : ℕ) : C k = {b ^ (k + 1) / n % b, b' ^ (k + 1) / n % b'} := by
    simp [C, hB, Finset.insert_val_of_notMem (Finset.notMem_singleton.mpr hne)]
  refine ⟨?_, congrArg Multiset.sum hC⟩
  -- The digit of `b` in column `i` lies in column `j`, and the two columns have the same sum.
  have hmem : b ^ (i + 1) / n % b ∈ C j := hC ▸ by simp [hCk]
  have hsum := congrArg Multiset.sum hC
  simp only [hCk, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
    Multiset.sum_cons, Multiset.sum_singleton] at hmem hsum
  simp only [D]
  omega

end MetaMathlibExt
