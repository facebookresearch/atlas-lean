/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Orders of two permutations and of their product (Kourovka Notebook Problem 18.49)

Kourovka Notebook, Archive of Solved Problems, Problem 18.49 (S. Kohl): let `n ∈ ℕ`. Is it true that
for any `a, b, c ∈ ℕ` with `1 < a, b, c ≤ n - 2` the symmetric group `Sₙ` has elements of order `a`
and `b` whose product has order `c`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.SymmetricGroupProductOrdersKourovka18Problem49Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.49 (S.
Kohl). UnsolvedMath record UM-00701478 (`KOU-18.49`), dataset ulamai/UnsolvedMath v1.8.0.

`Sₙ = Equiv.Perm (Fin n)`; for `n ≤ 3` there are no admissible `a, b, c`, and natural subtraction
matches `n - 2` there.
-/

/-- **Kohl's question on orders of products in symmetric groups.** For every natural number $n$
and all natural numbers $a, b, c$ with $1 < a \le n - 2$, $1 < b \le n - 2$ and $1 < c \le n - 2$,
the symmetric group $S_n$ contains permutations $x$ and $y$ such that $x$ has order $a$, $y$ has
order $b$ and $xy$ has order $c$. -/
def symmetricGroupHasProductWithOrders : Prop :=
  ∀ n a b c : ℕ, 1 < a → 1 < b → 1 < c → a ≤ n - 2 → b ≤ n - 2 → c ≤ n - 2 →
    ∃ x y : Equiv.Perm (Fin n), orderOf x = a ∧ orderOf y = b ∧ orderOf (x * y) = c

/-- **Permutations of prescribed orders with product of prescribed order.** For every natural
number $n$ and all natural numbers $a, b, c$ with $1 < a \le n - 2$, $1 < b \le n - 2$ and
$1 < c \le n - 2$, the symmetric group $S_n$ contains permutations $x$ and $y$ of orders $a$ and
$b$ whose product $xy$ has order $c$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 18.49 (S. Kohl); resolution: G. A. Miller, Amer. J. Math. 22 (1900), no. 2, 185-190; J.
König, European J. Combin. 57 (2016), 50-56, Kourovka Archive, Problem 18.49: Yes, it is (Miller);
another solution by König, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted symmetricGroupHasProductWithOrders_holds : symmetricGroupHasProductWithOrders

end MathlibExt.GroupTheory.SymmetricGroupProductOrdersKourovka18Problem49Wanted
