/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Group.Nat

/-!
# Disjunctive Rado numbers

Bounded representations with one scaled part and the admissible bounds for two-color
disjunctive Rado numbers, as studied by Srashti Dwivedi and Amitabha Tripathi.
-/

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
theorem exists_bounded_rep (a lam n N : ℕ)
    (ha : 3 ≤ a) (hn : 1 ≤ n) (hlam : a - 1 ≤ lam)
    (hN : N ≤ lam * (a + n)) :
    ∃ (x : ℕ → ℕ) (y : ℕ),
      (∀ i : ℕ, i < n → x i ≤ lam) ∧ y ≤ lam ∧
        (∑ i ∈ Finset.range n, x i) + a * y = N := by
  -- First choose the scaled part so that the ordinary parts can hold the remainder.
  obtain ⟨y, hy, r, hr, htotal⟩ : ∃ y ≤ lam, ∃ r ≤ lam * n, r + a * y = N := by
    by_cases h : a * lam ≤ N
    · refine ⟨lam, le_rfl, N - a * lam, ?_, Nat.sub_add_cancel h⟩
      rw [Nat.mul_add, Nat.mul_comm lam a] at hN
      omega
    · refine ⟨N / a, ?_, N % a, ?_, Nat.mod_add_div N a⟩
      · exact (Nat.div_lt_of_lt_mul (Nat.lt_of_not_ge h)).le
      · have hmod := Nat.mod_lt N (by omega : 0 < a)
        exact (show N % a ≤ lam by omega).trans (Nat.le_mul_of_pos_right lam hn)
  -- The first i ordinary parts contain min r (lam * i) in total.
  let s (i : ℕ) := min r (lam * i)
  have hs : Monotone s := fun _ _ hij => min_le_min_left r (Nat.mul_le_mul_left lam hij)
  refine ⟨fun i => s (i + 1) - s i, y, ?_, hy, ?_⟩
  · intro i _
    dsimp [s]
    rw [Nat.mul_succ]
    omega
  · rw [Finset.sum_range_tsub hs]
    simpa [s, min_eq_left hr] using htotal

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

end MathlibExt.Combinatorics.DisjunctiveRadoWanted
