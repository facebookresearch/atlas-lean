/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith

/-!
# Distinct multiples of `1, …, n` in an interval

Following P. Erdős and C. Pomerance, *Matching the natural numbers up to n with distinct
multiples in another interval*, Indag. Math. 83 (1980), 147–161, `f(n, m)` is the least `L`
such that the interval `(m, m + L]` contains distinct integers `a₁, …, aₙ` with `i ∣ aᵢ` for
every `i`. This file defines the interval predicate, the least length `f(n, m)`, and its
basic specification. It is shared by `WantedExt` statements from Wouter van Doorn, *On the
Length of an Interval That Contains Distinct Multiples of the First n Positive Integers*,
INTEGERS 26 (2026), Article A7, and by the Erdős Problem 711 entry in `OpenConjectures`.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Distinct multiples of $1, \dots, n$ in an interval.** For natural numbers $n$, $m$ and $L$,
the interval $(m, m + L]$ contains distinct multiples of $1, \dots, n$ when there are pairwise
distinct natural numbers $a_1, \dots, a_n$ with $m < a_i \le m + L$ and $i \mid a_i$ for every
$1 \le i \le n$.

Source: Wouter van Doorn, *On the Length of an Interval That Contains Distinct Multiples of the
First n Positive Integers*, INTEGERS 26 (2026), Article A7, Section 1 (definition of
`f(n, m)`, after Erdős and Pomerance). -/
def HasDistinctMultiplesInInterval (n m L : ℕ) : Prop :=
  ∃ a : Fin n → ℕ, Function.Injective a ∧
    ∀ i : Fin n, m < a i ∧ a i ≤ m + L ∧ (i.val + 1) ∣ a i

/-- **Least interval length containing distinct multiples.** For natural numbers $n$ and $m$,
$f(n, m)$ is the least natural number $L$ such that the interval $(m, m + L]$ contains distinct
multiples of $1, \dots, n$.

Such an $L$ always exists, so the least one is well defined.

Source: Wouter van Doorn, *On the Length of an Interval That Contains Distinct Multiples of the
First n Positive Integers*, INTEGERS 26 (2026), Article A7, Section 1 (definition of
`f(n, m)`, after Erdős and Pomerance). -/
noncomputable def distinctMultiplesIntervalLength (n m : ℕ) : ℕ :=
  sInf {L | HasDistinctMultiplesInInterval n m L}

/-- **Lengthening the interval preserves distinct multiples.** For natural numbers $n$, $m$, $L$
and $L'$ with $L \le L'$, if the interval $(m, m + L]$ contains distinct multiples of
$1, \dots, n$, then so does the interval $(m, m + L']$.

Source: Wouter van Doorn, *On the Length of an Interval That Contains Distinct Multiples of the
First n Positive Integers*, INTEGERS 26 (2026), Article A7, Section 1 (definition of
`f(n, m)`). -/
theorem HasDistinctMultiplesInInterval.mono {n m L L' : ℕ} (hLL' : L ≤ L')
    (h : HasDistinctMultiplesInInterval n m L) : HasDistinctMultiplesInInterval n m L' := by
  obtain ⟨a, ha, hb⟩ := h
  exact ⟨a, ha, fun i => ⟨(hb i).1, le_trans (hb i).2.1 (by omega), (hb i).2.2⟩⟩

/-- **Some interval contains distinct multiples.** For all natural numbers $n$ and $m$ there is a
natural number $L$ such that the interval $(m, m + L]$ contains distinct multiples of
$1, \dots, n$.

For example, $L = n(m + 1)$ works, with $a_i = i(m + 1)$ for $1 \le i \le n$.

Source: Wouter van Doorn, *On the Length of an Interval That Contains Distinct Multiples of the
First n Positive Integers*, INTEGERS 26 (2026), Article A7, Section 1 (definition of
`f(n, m)`). -/
theorem exists_hasDistinctMultiplesInInterval (n m : ℕ) :
    ∃ L, HasDistinctMultiplesInInterval n m L := by
  refine ⟨n * (m + 1), fun i => (i.val + 1) * (m + 1), ?_, fun i => ⟨?_, ?_, ?_⟩⟩
  · intro i j hij
    exact Fin.ext (by simpa using Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m) hij)
  · nlinarith
  · have := i.isLt
    nlinarith
  · exact dvd_mul_right _ _

/-- **The least interval length is admissible.** For natural numbers $n$ and $m$, let $f(n, m)$
be the least natural number $L$ such that the interval $(m, m + L]$ contains distinct multiples
of $1, \dots, n$. Then the interval $(m, m + f(n, m)]$ contains distinct multiples of
$1, \dots, n$.

Source: Wouter van Doorn, *On the Length of an Interval That Contains Distinct Multiples of the
First n Positive Integers*, INTEGERS 26 (2026), Article A7, Section 1 (definition of
`f(n, m)`). -/
theorem hasDistinctMultiplesInInterval_distinctMultiplesIntervalLength (n m : ℕ) :
    HasDistinctMultiplesInInterval n m (distinctMultiplesIntervalLength n m) :=
  Nat.sInf_mem (exists_hasDistinctMultiplesInInterval n m)

/-- **Characterization of the least interval length.** For natural numbers $n$ and $m$, let
$f(n, m)$ be the least natural number $K$ such that the interval $(m, m + K]$ contains distinct
multiples of $1, \dots, n$. Then for every natural number $L$, $f(n, m) \le L$ if and only if
the interval $(m, m + L]$ contains distinct multiples of $1, \dots, n$.

Source: Wouter van Doorn, *On the Length of an Interval That Contains Distinct Multiples of the
First n Positive Integers*, INTEGERS 26 (2026), Article A7, Section 1 (definition of
`f(n, m)`). -/
theorem distinctMultiplesIntervalLength_le_iff {n m L : ℕ} :
    distinctMultiplesIntervalLength n m ≤ L ↔ HasDistinctMultiplesInInterval n m L :=
  ⟨fun h => (hasDistinctMultiplesInInterval_distinctMultiplesIntervalLength n m).mono h,
    fun h => Nat.sInf_le h⟩

/-- **The least interval length for $n = 1$.** For natural numbers $n$ and $m$, let $f(n, m)$ be
the least natural number $L$ such that the interval $(m, m + L]$ contains distinct multiples of
$1, \dots, n$. Then $f(1, m) = 1$ for every natural number $m$: the interval $(m, m + 1]$
contains the multiple $m + 1$ of $1$, and the empty interval $(m, m]$ contains nothing.

Source: Wouter van Doorn, *On the Length of an Interval That Contains Distinct Multiples of the
First n Positive Integers*, INTEGERS 26 (2026), Article A7, Section 1 (definition of
`f(n, m)`). -/
theorem distinctMultiplesIntervalLength_one (m : ℕ) :
    distinctMultiplesIntervalLength 1 m = 1 := by
  apply le_antisymm
  · refine Nat.sInf_le ⟨fun _ => m + 1, fun _ _ _ => Subsingleton.elim _ _, fun i => ?_⟩
    obtain rfl := Subsingleton.elim i 0
    simp
  · refine le_csInf ⟨1, fun _ => m + 1, fun _ _ _ => Subsingleton.elim _ _, fun i => ?_⟩ ?_
    · obtain rfl := Subsingleton.elim i 0
      simp
    rintro L ⟨a, -, ha⟩
    have := ha 0
    omega

end MetaMathlibExt
