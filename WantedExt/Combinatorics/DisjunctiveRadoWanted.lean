/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Order.Bounds.Defs
public import MathlibExt.Combinatorics.DisjunctiveRado
public import MathlibExt.Combinatorics.DisjunctiveRadoParity
public import MathlibExt.Combinatorics.DisjunctiveRadoSingleton

/-!
# Two-color disjunctive Rado numbers

Statements from Srashti Dwivedi and Amitabha Tripathi, "On the Two-Color Disjunctive Rado
Number for the Equations `∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j`, `j = 1, 2`",
*INTEGERS* 25 (2025), Article A108.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.DisjunctiveRadoWanted

/-- **Theorem 3** (quoted): let `a ≥ 3`, `m ≥ 3` have the same parity and
`a' = a + m - 3`. If (i) `m = 3` and `c ≤ -a(a-3)/2`, or (ii) `m ≥ 4` and
`c < -(a' + 3)(a - 2)`, then the Rado number of
`∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c` is `(a' + 3)(a' - c) + 1`.

Source: Srashti Dwivedi and Amitabha Tripathi, "On the Two-Color Disjunctive
Rado Number for the Equations `∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j`,
`j = 1, 2`", INTEGERS 25 (2025), Article A108, Theorem 3 (from [4, Theorem 3]
and [5, Theorem 5]). -/
theorem_wanted isLeast_disjRadoSet_single (a m : ℕ) (c : ℤ) (ha : 3 ≤ a) (hm : 3 ≤ m)
    (hpar : a % 2 = m % 2)
    (hc : (m = 3 ∧ c ≤ -((a : ℤ) * (a - 3) / 2)) ∨
      (4 ≤ m ∧ c < -(((a : ℤ) + m - 3 + 3) * (a - 2)))) :
    IsLeast (disjRadoSet m a {c}) ((((a : ℤ) + m - 3 + 3) * ((a : ℤ) + m - 3 - c) + 1).toNat)

/-- **Theorem 5**: for `4 ≤ m ≤ a` and `c_j = k_j (a + m - 3)` with
`1 < k_j ≤ a + m - 2`, `R(c₁, c₂) = min {k₁, k₂}`.

Source: Srashti Dwivedi and Amitabha Tripathi, "On the Two-Color Disjunctive
Rado Number for the Equations `∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j`,
`j = 1, 2`", INTEGERS 25 (2025), Article A108, Theorem 5. -/
theorem_wanted isLeast_disjRadoSet_multiples (a m k₁ k₂ : ℕ) (hm : 4 ≤ m) (hma : m ≤ a)
    (hk₁ : 1 < k₁) (hk₁' : k₁ ≤ a + m - 2) (hk₂ : 1 < k₂) (hk₂' : k₂ ≤ a + m - 2) :
    IsLeast (disjRadoSet m a {(k₁ : ℤ) * (a + m - 3), (k₂ : ℤ) * (a + m - 3)}) (min k₁ k₂)

/-- **Theorem 6**: let `a ≥ 3`, `m ≥ 4` have the same parity, `a' = a + m - 3` and
`c₁ < -(a' + 3)(a - 2)`. For `c₂ ≤ c₁` (the range covered by the paper's four
cases),
(4a) `R(c₁, c₂) = (a' + 3)(a' - c₁) + 1` if `c₁ - a' ≤ c₂`;
(4b) `(a' + 2)(a' - c₁) + 1` if `(a' + 2)c₁ - a'(a' + 1) ≤ c₂ < c₁ - a'`;
(4c) `(a' - c₂) + 1` if `(a' + 3)c₁ - a'(a' + 2) < c₂ < (a' + 2)c₁ - a'(a' + 1)`;
(4d) `(a' + 3)(a' - c₁) + 1` if `c₂ ≤ (a' + 3)c₁ - a'(a' + 2)`.

Source: Srashti Dwivedi and Amitabha Tripathi, "On the Two-Color Disjunctive
Rado Number for the Equations `∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j`,
`j = 1, 2`", INTEGERS 25 (2025), Article A108, Theorem 6. -/
theorem_wanted isLeast_disjRadoSet_pair (a m : ℕ) (c₁ c₂ : ℤ) (ha : 3 ≤ a) (hm : 4 ≤ m)
    (hpar : a % 2 = m % 2) (hc₁ : c₁ < -(((a : ℤ) + m - 3 + 3) * (a - 2))) (hc₂ : c₂ ≤ c₁) :
    let a' : ℤ := a + m - 3
    (c₁ - a' ≤ c₂ →
        IsLeast (disjRadoSet m a {c₁, c₂}) ((a' + 3) * (a' - c₁) + 1).toNat) ∧
      ((a' + 2) * c₁ - a' * (a' + 1) ≤ c₂ → c₂ < c₁ - a' →
        IsLeast (disjRadoSet m a {c₁, c₂}) ((a' + 2) * (a' - c₁) + 1).toNat) ∧
      ((a' + 3) * c₁ - a' * (a' + 2) < c₂ → c₂ < (a' + 2) * c₁ - a' * (a' + 1) →
        IsLeast (disjRadoSet m a {c₁, c₂}) (a' - c₂ + 1).toNat) ∧
      (c₂ ≤ (a' + 3) * c₁ - a' * (a' + 2) →
        IsLeast (disjRadoSet m a {c₁, c₂}) ((a' + 3) * (a' - c₁) + 1).toNat)

end MathlibExt.Combinatorics.DisjunctiveRadoWanted
