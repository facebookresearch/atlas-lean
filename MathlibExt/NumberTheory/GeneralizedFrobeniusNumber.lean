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

/-- The number `d(m; a₁, …, a_k)` of representations of an integer `m` as `x₁a₁ + ⋯ + x_ka_k` with
`xᵢ ∈ ℕ`, as an extended natural number: it is `0` for `m < 0`, finite when every generator is
positive, and `⊤` when the representation set is infinite.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction (definition of `d(n; a₁, …, a_k)`). -/
noncomputable def frobeniusRepCount {k : ℕ} (a : Fin k → ℕ) (m : ℤ) : ℕ∞ :=
  {x : Fin k → ℕ | ∑ i, (x i : ℤ) * a i = m}.encard

/-- A negative integer has no representation.

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

/-- With positive generators every integer has finitely many representations.

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

/-- `g` is the generalized Frobenius number `g(a; s) = max {m ∈ ℤ | d(m; a) ≤ s}`: `g` has at most
`s` representations and every larger integer has more than `s`.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction (definition of `g(A; s)`). -/
def IsGenFrobeniusNumber {k : ℕ} (a : Fin k → ℕ) (s : ℕ) (g : ℤ) : Prop :=
  frobeniusRepCount a g ≤ s ∧ ∀ m : ℤ, g < m → (s : ℕ∞) < frobeniusRepCount a m

/-- The generalized Frobenius number is unique.

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
