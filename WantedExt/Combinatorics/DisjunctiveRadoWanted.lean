/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Two-color disjunctive Rado numbers

Statement from Srashti Dwivedi and Amitabha Tripathi,
"On the Two-Color Disjunctive Rado Number for the Equations
`∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j`, `j = 1, 2`",
*INTEGERS* 25 (2025), Article A108
(<https://math.colgate.edu/~integers/vol25.html>).

Proposition 4 is the paper's self-contained covering lemma:
with `λ ≥ a - 1`, every `N ≤ λ (a + n)` is a sum
`x_1 + ⋯ + x_n + a x_{n+1}` with all parts at most `λ`.
It was verified by exhaustive search for `3 ≤ a ≤ 8`,
`a - 1 ≤ λ ≤ a + 4`, `1 ≤ n ≤ 5`.

Not stated (see the source audit table): Proposition 2 and
Theorems 1, 3, 5, 6, which concern the disjunctive Rado
number `R(c_1, c_2)`, a notion not defined in the
extracted statements.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.DisjunctiveRadoWanted

/-- **Bounded representations with one scaled part.** Let $a$, $\lambda$, $n$ and $N$ be natural
numbers with $a \ge 3$, $n \ge 1$, $\lambda \ge a - 1$ and $N \le \lambda (a + n)$. Then there are
natural numbers $x_0, \dots, x_{n-1}$ and $y$, each at most $\lambda$, such that
$x_0 + \dots + x_{n-1} + a y = N$.

The endpoint $N = 0$ is included as in the paper's displayed range $\{0, \dots, \lambda(a + n)\}$;
that case is trivial, all parts being $0$.

Source: Srashti Dwivedi and Amitabha Tripathi, "On the
Two-Color Disjunctive Rado Number for the Equations
`∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j`, `j = 1, 2`",
Proposition 4. -/
theorem_wanted exists_bounded_rep (a lam n N : ℕ)
    (ha : 3 ≤ a) (hn : 1 ≤ n) (hlam : a - 1 ≤ lam)
    (hN : N ≤ lam * (a + n)) :
    ∃ (x : ℕ → ℕ) (y : ℕ),
      (∀ i : ℕ, i < n → x i ≤ lam) ∧ y ≤ lam ∧
        (∑ i ∈ Finset.range n, x i) + a * y = N

end MathlibExt.Combinatorics.DisjunctiveRadoWanted
