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

Also stated: the disjunctive Rado number `R(c_1, c_2)` (least
`R ≥ 1` such that every 2-colouring of `[1, R]` has a
monochromatic solution of one equation), Theorem 1 and
Proposition 2 (quoted nonexistence and `R = 1`), Theorem 3
(quoted single-equation values), Theorem 5 and Theorem 6.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Int.Defs

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.DisjunctiveRadoWanted

/-- **Proposition 4**: let `a, λ, n` be natural numbers
with `a ≥ 3`, `n ≥ 1` and `λ ≥ a - 1`. Then for each
`N ∈ {0, …, λ (a + n)}` the equation
`∑ i in Finset.range n, x i + a * y = N` admits a
solution with each part in `{0, …, λ}`. (The endpoint
`N = 0` is included as in the paper's displayed range
`{0, …, λ(a + n)}`; that case is trivial, all parts
being `0`.)

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

/-- `radoGood m a cs R`: every 2-colouring of `[1, R]` admits, for some `c ∈ cs`,
a monochromatic solution of `∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c` with all
variables in `[1, R]` (colourings are maps `ℕ → Bool`, only their values on
`[1, R]` matter).

Source: Srashti Dwivedi and Amitabha Tripathi, "On the Two-Color Disjunctive
Rado Number for the Equations `∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j`,
`j = 1, 2`", INTEGERS 25 (2025), Article A108, Section 1 (definition of the
2-color disjunctive Rado number). -/
def radoGood (m : ℕ) (a : ℤ) (cs : Finset ℤ) (R : ℕ) : Prop :=
  ∀ col : ℕ → Bool, ∃ c ∈ cs, ∃ x : Fin (m - 2) → ℕ, ∃ y z : ℕ,
    (∀ i, x i ∈ Finset.Icc 1 R) ∧ y ∈ Finset.Icc 1 R ∧ z ∈ Finset.Icc 1 R ∧
      (∀ i, col (x i) = col y) ∧ col z = col y ∧
        ∑ i, (x i : ℤ) + a * y - z = c

/-- The admissible bounds `R ≥ 1` of the disjunctive Rado problem; the
disjunctive Rado number `R(cs)` is the least element of this set, when it is
nonempty.

Source: Srashti Dwivedi and Amitabha Tripathi, "On the Two-Color Disjunctive
Rado Number for the Equations `∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j`,
`j = 1, 2`", INTEGERS 25 (2025), Article A108, Section 1. -/
def disjRadoSet (m : ℕ) (a : ℤ) (cs : Finset ℤ) : Set ℕ :=
  {R | 1 ≤ R ∧ radoGood m a cs R}

/-- `radoGood` is monotone in `R`, so `disjRadoSet` is an up-set and its least
element is the threshold.

Source: Srashti Dwivedi and Amitabha Tripathi, "On the Two-Color Disjunctive
Rado Number for the Equations `∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j`,
`j = 1, 2`", INTEGERS 25 (2025), Article A108, Section 1. -/
theorem radoGood_mono {m : ℕ} {a : ℤ} {cs : Finset ℤ} {R R' : ℕ} (h : R ≤ R')
    (hR : radoGood m a cs R) : radoGood m a cs R' := by
  intro col
  obtain ⟨c, hc, x, y, z, hx, hy, hz, hxc, hzc, he⟩ := hR col
  refine ⟨c, hc, x, y, z, fun i => ?_, ?_, ?_, hxc, hzc, he⟩
  · have := hx i
    simp only [Finset.mem_Icc] at this ⊢
    omega
  · simp only [Finset.mem_Icc] at hy ⊢
    omega
  · simp only [Finset.mem_Icc] at hz ⊢
    omega

/-- **Theorem 1** (quoted from the authors' earlier paper): for `4 ≤ m ≤ a` with
`a + m` and `c` odd, the Rado number of
`∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c` does not exist: no `R` has the
monochromatic-solution property.

Source: Srashti Dwivedi and Amitabha Tripathi, "On the Two-Color Disjunctive
Rado Number for the Equations `∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j`,
`j = 1, 2`", INTEGERS 25 (2025), Article A108, Theorem 1 (from [5, Theorem 1]). -/
theorem_wanted not_radoGood_of_odd (a m : ℕ) (c : ℤ) (hm : 4 ≤ m) (hma : m ≤ a)
    (ham : Odd (a + m)) (hc : Odd c) (R : ℕ) : ¬ radoGood m a {c} R

/-- **Proposition 2** (quoted): for `4 ≤ m ≤ a`, the Rado number of
`∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = a + m - 3` is `1`.

Source: Srashti Dwivedi and Amitabha Tripathi, "On the Two-Color Disjunctive
Rado Number for the Equations `∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j`,
`j = 1, 2`", INTEGERS 25 (2025), Article A108, Proposition 2 (from
[5, Proposition 1]). -/
theorem_wanted isLeast_disjRadoSet_eq_one (a m : ℕ) (hm : 4 ≤ m) (hma : m ≤ a) :
    IsLeast (disjRadoSet m a {(a : ℤ) + m - 3}) 1

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
