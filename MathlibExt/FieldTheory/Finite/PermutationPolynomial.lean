/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Permutation polynomials complete to level `k`

Source: S. Rajagopal and P. Vanchinathan, *Higher Level Completeness for
Permutation Polynomials* (arXiv `2310.12466v1`). A polynomial `f ∈ F_q[X]` is
complete to level `k` (`k`-complete) when `f` together with `f + x`, …,
`f + kx` are all permutation polynomials.
-/

@[expose] public section

namespace Polynomial

/-- **Permutation polynomial over a finite field.** A polynomial $f$ over a finite field $F$ is a
permutation polynomial when its evaluation map $F \to F$, $x \mapsto f(x)$, is bijective. -/
def IsPermutationPolynomial {F : Type*} [Field F] [Finite F]
    (f : Polynomial F) : Prop :=
  Function.Bijective fun x => f.eval x

/-- **Polynomial complete to level $k$.** Let $F$ be a finite field,
$f \in F[X]$ and $k$ a natural number. The polynomial $f$ is complete to level $k$ ($k$-complete)
when $f + iX$ is a permutation polynomial for every natural number $i \le k$, where $i$ is viewed
as an element of $F$.

The source considers only positive levels $k$; here every natural level is allowed, and
completeness to level $0$ says that $f$ itself is a permutation polynomial. -/
def IsKComplete {F : Type*} [Field F] [Finite F] (f : Polynomial F)
    (k : ℕ) : Prop :=
  ∀ i : ℕ, i ≤ k → IsPermutationPolynomial (f + Polynomial.C (i : F) * Polynomial.X)

/-- **Unfolded form of $k$-completeness.** Let $F$ be a finite field, $f \in F[X]$ and $k$ a
natural number. Then $f$ is complete to level $k$ if and only if for every natural number
$i \le k$ the map $F \to F$, $x \mapsto (f + iX)(x)$, is bijective, where $i$ is viewed as an
element of $F$. -/
theorem isKComplete_iff {F : Type*} [Field F] [Finite F] (f : Polynomial F)
    (k : ℕ) :
    IsKComplete f k ↔ ∀ i : ℕ, i ≤ k →
      Function.Bijective fun x =>
        (f + Polynomial.C (i : F) * Polynomial.X).eval x :=
  Iff.rfl

/-- **Completeness at a lower level.** Let $F$ be a finite field, $f \in F[X]$ and let $j \le k$
be natural numbers. If $f$ is complete to level $k$, then $f$ is complete to level $j$. -/
theorem isKComplete_mono {F : Type*} [Field F] [Finite F] {f : Polynomial F}
    {j k : ℕ} (h : IsKComplete f k) (hle : j ≤ k) : IsKComplete f j :=
  fun i hi => h i (le_trans hi hle)

/-- **Completeness at level zero.** Let $F$ be a finite field and $f \in F[X]$. Then $f$ is
complete to level $0$ if and only if $f$ is a permutation polynomial. -/
theorem isKComplete_zero {F : Type*} [Field F] [Finite F] (f : Polynomial F) :
    IsKComplete f 0 ↔ IsPermutationPolynomial f := by
  constructor
  · intro h
    have h0 := h 0 le_rfl
    simpa using h0
  · intro h i hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    simpa using h

/-- **Completeness at the next level.** Let $F$ be a finite field, $f \in F[X]$ and $k$ a natural
number. Then $f$ is complete to level $k + 1$ if and only if $f$ is complete to level $k$ and
$f + (k + 1)X$ is a permutation polynomial, where $k + 1$ is viewed as an element of $F$. -/
theorem isKComplete_succ_iff {F : Type*} [Field F] [Finite F]
    (f : Polynomial F) (k : ℕ) :
    IsKComplete f (k + 1) ↔ IsKComplete f k ∧
      IsPermutationPolynomial
        (f + Polynomial.C ((k + 1 : ℕ) : F) * Polynomial.X) := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (le_trans hi (Nat.le_succ k)), h (k + 1) le_rfl⟩
  · intro h i hi
    rcases eq_or_lt_of_le hi with rfl | hlt
    · exact h.2
    · exact h.1 i (Nat.le_of_lt_add_one hlt)

/-- **A $k$-complete polynomial is a permutation polynomial.** Let $F$ be a finite field,
$f \in F[X]$ and $k$ a natural number. If $f$ is complete to level $k$, then $f$ is a
permutation polynomial. -/
theorem isKComplete_self {F : Type*} [Field F] [Finite F] {f : Polynomial F}
    {k : ℕ} (h : IsKComplete f k) : IsPermutationPolynomial f := by
  have h0 := h 0 (Nat.zero_le k)
  simpa using h0

end Polynomial
