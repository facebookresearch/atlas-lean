/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Card

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval

/-!
# Ordered signed sums of squares
Ordered signed integer vectors and their representation numbers.
-/

@[expose] public section

namespace SumSquares

/-- **Integer solutions of a sum of squares.** For natural numbers $k$ and $n$, the solution set
is the set of all integer vectors $x = (x_1, \dots, x_k) \in \mathbb{Z}^k$ with
$x_1^2 + \cdots + x_k^2 = n$. -/
def solutions (k n : ℕ) : Set (Fin k → ℤ) :=
  { x | dotProduct x x = (n : ℤ) }

/-- **Representation numbers of sums of squares.** For natural numbers $k$ and $n$, the
representation number $r_k(n)$ is the number of elements of the solution set, that is, the
number of integer vectors $(x_1, \dots, x_k) \in \mathbb{Z}^k$ with $x_1^2 + \cdots + x_k^2 = n$.
Representations that differ in the order or the signs of the entries are counted separately. -/
noncomputable def representationNumber (k n : ℕ) : ℕ :=
  (solutions k n).ncard

@[simp]
theorem mem_solutions {k n : ℕ} {x : Fin k → ℤ} :
    x ∈ solutions k n ↔ dotProduct x x = (n : ℤ) :=
  Iff.rfl

/-- **Finitely many representations as a sum of squares.** For all natural numbers $k$ and $n$,
there are only finitely many integer vectors $(x_1, \dots, x_k) \in \mathbb{Z}^k$ with
$x_1^2 + \cdots + x_k^2 = n$. -/
theorem solutions_finite (k n : ℕ) : Set.Finite (solutions k n) := by
  apply (Set.Finite.pi fun _ => Set.finite_Icc (-(n : ℤ)) (n : ℤ)).subset
  intro x hx
  rw [Set.mem_pi]
  intro i _
  rw [Set.mem_Icc]
  have hsq : x i ^ 2 ≤ (n : ℤ) := by
    rw [← (mem_solutions.mp hx)]
    simpa only [dotProduct, pow_two] using
      Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (x j))
        (Finset.mem_univ i)
  have habs : |x i| ≤ (n : ℤ) := by
    simpa only [Int.natCast_natAbs] using (Int.natAbs_le_self_sq (x i)).trans hsq
  exact abs_le.mp habs

/-- **The representation number counts a finite set.** For all natural numbers $k$ and $n$, the
representation number $r_k(n)$ equals the number of elements of the finite solution set of
integer vectors $(x_1, \dots, x_k) \in \mathbb{Z}^k$ with $x_1^2 + \cdots + x_k^2 = n$. -/
theorem representationNumber_eq_toFinset_card (k n : ℕ) :
    representationNumber k n = (solutions_finite k n).toFinset.card := by
  exact Set.ncard_eq_toFinset_card _ _

/-- **The zero vector represents zero as a sum of squares.** For every $k \in \mathbb{N}$, the
zero vector of $\mathbb{Z}^k$ has squared norm $0$, that is, it lies in the set of integer
vectors $x \in \mathbb{Z}^k$ with $x_1^2 + \cdots + x_k^2 = 0$. -/
theorem zero_mem_solutions (k : ℕ) :
    (0 : Fin k → ℤ) ∈ solutions k 0 := by
  simp [mem_solutions, dotProduct]

theorem zero_notMem_solutions_succ (k n : ℕ) :
    (0 : Fin k → ℤ) ∉ solutions k (n + 1) := by
  simp only [mem_solutions]
  intro h
  have h0 : dotProduct (0 : Fin k → ℤ) (0 : Fin k → ℤ) = 0 := by
    simp [dotProduct]
  rw [h0] at h
  have hne : ((n + 1 : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  exact hne h.symm

@[simp]
theorem neg_mem_iff {k n : ℕ} {x : Fin k → ℤ} :
    (-x) ∈ solutions k n ↔ x ∈ solutions k n := by
  simp [mem_solutions, neg_dotProduct, dotProduct_neg]

/-- **Solution set of the empty sum at zero.** The set of vectors $x \in \mathbb{Z}^0$
whose sum of squares (an empty sum) equals $0$ is all of $\mathbb{Z}^0$. -/
theorem solutions_zero_zero : solutions 0 0 = Set.univ := by
  ext x
  simp [mem_solutions, dotProduct]

/-- **Zero squares never sum to a positive integer.** For every natural number $n \ge 1$, no
vector $x \in \mathbb{Z}^0$ has sum of squares equal to $n$; that is, the solution set is empty. -/
theorem solutions_zero_succ (n : ℕ) : solutions 0 (n + 1) = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, mem_solutions, iff_false]
  intro h
  have h0 : dotProduct x x = 0 := by
    simp [dotProduct]
  have heq : ((n + 1 : ℕ) : ℤ) = 0 := by
    calc ((n + 1 : ℕ) : ℤ) = dotProduct x x := h.symm
      _ = 0 := h0
  have hne : ((n + 1 : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  exact hne heq

/-- **Solution set of one square equal to zero.** The set of vectors $x \in \mathbb{Z}^1$
with $x_1^2 = 0$ consists of the zero vector alone. -/
theorem solutions_one_zero : solutions 1 0 = {(0 : Fin 1 → ℤ)} := by
  ext x
  simp only [mem_solutions, Set.mem_singleton_iff]
  have hDot : dotProduct x x = x (0 : Fin 1) * x 0 := by
    simp only [dotProduct]
    have hU : (Finset.univ : Finset (Fin 1)) = {(0 : Fin 1)} := by
      ext i
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim _ _
    rw [hU, Finset.sum_singleton]
  rw [hDot]
  have hx : x = (0 : Fin 1 → ℤ) ↔ x (0 : Fin 1) = 0 := by
    constructor
    · intro h
      exact congr_fun h 0
    · intro h0
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      rw [hi, h0, Pi.zero_apply]
  rw [hx]
  simp [mul_eq_zero]

/-- **Zero as a sum of zero squares.** The representation number $r_0(0)$, the number of integer
vectors $x \in \mathbb{Z}^0$ whose sum of squares (an empty sum) equals $0$, is $1$. -/
theorem representationNumber_zero_zero : representationNumber 0 0 = 1 := by
  simp [representationNumber, solutions_zero_zero, Set.ncard_univ]

/-- **Positive integers have no representation as a sum of zero squares.** For every natural
number $n \ge 1$, the representation number $r_0(n)$, the number of integer vectors
$x \in \mathbb{Z}^0$ whose sum of squares (an empty sum) equals $n$, is $0$. -/
theorem representationNumber_zero_succ (n : ℕ) :
    representationNumber 0 (n + 1) = 0 := by
  simp [representationNumber, solutions_zero_succ]

/-- **Zero as a sum of one square.** The representation number $r_1(0)$, the number of integer
vectors $x \in \mathbb{Z}^1$ with $x_1^2 = 0$, equals $1$. -/
theorem representationNumber_one_zero : representationNumber 1 0 = 1 := by
  simp [representationNumber, solutions_one_zero]

end SumSquares
