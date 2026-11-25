/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Set.Card
import Mathlib.Data.Pi.Interval
import Mathlib.Order.Interval.Finset.Nat

/-! # Generalized Frobenius numbers

The representation count `d(m; a₁, …, a_k)` of an integer `m` by a vector of natural generators,
valued in `ℕ∞` so that an infinite representation set (possible only with a zero generator) counts
as `⊤` rather than collapsing to `0`, and the predicate `IsGenFrobeniusNumber a s g` saying that
`g = max {m ∈ ℤ | d(m; a) ≤ s}` is the generalized Frobenius number `g(a; s)`.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction (definitions of `d(n; a₁, …, a_k)` and
`g(A; s)`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Number of representations by a vector of generators.** For natural numbers
$a_1, \dots, a_k$ and an integer $m$, the representation count $d(m; a_1, \dots, a_k)$ is the
number of tuples $(x_1, \dots, x_k)$ of natural numbers with $x_1 a_1 + \dots + x_k a_k = m$,
counted as an extended natural number, so that it is $\infty$ when there are infinitely many such
tuples.

It is $0$ for $m < 0$, and finite when every $a_i$ is positive.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction (definition of `d(n; a₁, …, a_k)`). -/
noncomputable def frobeniusRepCount {k : ℕ} (a : Fin k → ℕ) (m : ℤ) : ℕ∞ :=
  {x : Fin k → ℕ | ∑ i, (x i : ℤ) * a i = m}.encard

/-- **Negative integers have no representations.** For all natural numbers $a_1, \dots, a_k$ and
every integer $m < 0$, the representation count $d(m; a_1, \dots, a_k)$ is $0$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction (definition of `d(n; a₁, …, a_k)`). -/
theorem frobeniusRepCount_eq_zero_of_neg {k : ℕ} (a : Fin k → ℕ) {m : ℤ} (hm : m < 0) :
    frobeniusRepCount a m = 0 := by
  rw [frobeniusRepCount, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  intro x (hx : ∑ i, (x i : ℤ) * a i = m)
  have : 0 ≤ ∑ i, (x i : ℤ) * a i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
  rw [hx] at this
  omega

/-- **Finitely many representations for positive generators.** If $a_1, \dots, a_k$ are positive
natural numbers, then for every integer $m$ the representation count $d(m; a_1, \dots, a_k)$ is
finite.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction (definition of `d(n; a₁, …, a_k)`). -/
theorem frobeniusRepCount_ne_top {k : ℕ} {a : Fin k → ℕ} (ha : ∀ i, 0 < a i) (m : ℤ) :
    frobeniusRepCount a m ≠ ⊤ := by
  rw [frobeniusRepCount, Set.encard_ne_top_iff]
  refine (Set.finite_Iic (fun _ : Fin k => m.toNat)).subset ?_
  intro x hx j
  have hx : ∑ i, (x i : ℤ) * a i = m := hx
  have hle : (x j : ℤ) * a j ≤ ∑ i, (x i : ℤ) * a i :=
    Finset.single_le_sum (f := fun i => (x i : ℤ) * a i)
      (fun i _ => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)) (Finset.mem_univ j)
  have h1 : (x j : ℤ) ≤ (x j : ℤ) * a j :=
    le_mul_of_one_le_right (Int.natCast_nonneg _) (by exact_mod_cast ha j)
  show x j ≤ m.toNat
  omega

/-- **Generalized Frobenius number.** For natural numbers $a_1, \dots, a_k$ and $s$, write
$d(m; a)$ for the number of representations of an integer $m$ by $a = (a_1, \dots, a_k)$. An
integer $g$ is the generalized Frobenius number $g(a; s) = \max \{m \in \mathbb{Z} \mid
d(m; a) \le s\}$ when $d(g; a) \le s$ and $d(m; a) > s$ for every integer $m > g$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction (definition of `g(A; s)`). -/
def IsGenFrobeniusNumber {k : ℕ} (a : Fin k → ℕ) (s : ℕ) (g : ℤ) : Prop :=
  frobeniusRepCount a g ≤ s ∧ ∀ m : ℤ, g < m → (s : ℕ∞) < frobeniusRepCount a m

/-- **Uniqueness of the generalized Frobenius number.** For natural numbers $a_1, \dots, a_k$ and
$s$, if the integers $g$ and $g'$ are both the generalized Frobenius number $g(a_1, \dots, a_k; s)$,
then $g = g'$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction (definition of `g(A; s)` as a maximum). -/
theorem IsGenFrobeniusNumber.unique {k : ℕ} {a : Fin k → ℕ} {s : ℕ} {g g' : ℤ}
    (h : IsGenFrobeniusNumber a s g) (h' : IsGenFrobeniusNumber a s g') : g = g' := by
  rcases lt_trichotomy g g' with hlt | heq | hgt
  · exact absurd h'.1 (not_le.2 (h.2 g' hlt))
  · exact heq
  · exact absurd h.1 (not_le.2 (h'.2 g hgt))

end

end MetaMathlibExt
