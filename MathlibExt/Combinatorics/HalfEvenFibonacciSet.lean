/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.AccessibleSets

/-!
# Halves of even Fibonacci numbers and $4$-accessibility of the Fibonacci numbers

Let $f_n$ be the $n$-th Fibonacci number, with $f_0 = 0$ and $f_1 = 1$. This file defines the set
`halfEvenFibonacciSet`, $G = \{f_{3n}/2 : n \ge 1\} = \{1, 4, 17, 72, \dots\}$, of halves of the
positive even Fibonacci numbers, and proves Wesley's reduction
`not_accessible_four_of_halfEvenFibonacci`: if $G$ is not $2$-accessible, then the set
$F = \{1, 2, 3, 5, 8, \dots\}$ of positive Fibonacci numbers is not $4$-accessible.

## Main declarations

* `MetaMathlibExt.halfEvenFibonacciSet`: the set $G$, with `four_mem_halfEvenFibonacciSet`.
* `MetaMathlibExt.not_accessible_four_of_halfEvenFibonacci`: if $G$ is not $2$-accessible, then
  $F$ is not $4$-accessible.

## Implementation notes

Wesley colors a positive integer $n$ by its parity and by the color of $\lceil n/2 \rceil$ under a
$2$-coloring with no long monochromatic $G$-diffsequence. Here the parity refinement is
`accessible_divisible_subset` with $d = 2$: if $F$ were $4$-accessible, the set of its even
members would be $2$-accessible. The terms of a diffsequence with even gaps all have the same
parity, so $n \mapsto \lceil n/2 \rceil$ halves its gaps, and half of an even positive Fibonacci
number lies in $G$, because $f_m$ is even only when $3 \mid m$. Coloring $n$ by the color of
$\lceil n/2 \rceil$ therefore turns long monochromatic diffsequences with even Fibonacci gaps into
long monochromatic $G$-diffsequences.

## References

* William J. Wesley, *Improved Ramsey-type theorems for Fibonacci numbers and other sequences*,
  INTEGERS 25 (2025), Article A29; preprint arXiv:2211.05167, Lemma 7 and its proof.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Halves of even Fibonacci numbers.** Let $F_m$ be the $m$-th Fibonacci number, with $F_0 = 0$
and $F_1 = 1$. The set of halves of the positive even Fibonacci numbers is
$G = \{F_{3n}/2 : n \ge 1\} = \{1, 4, 17, 72, \dots\}$; its elements are written
$g_n = F_{3n}/2$ for $n \ge 1$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Section 2 (notation `G`, `g_n`). -/
def halfEvenFibonacciSet : Set ℕ :=
  Set.range fun n => Nat.fib (3 * (n + 1)) / 2

/-- **$4$ is half of an even Fibonacci number.** Let $F_m$ be the $m$-th Fibonacci number, with
$F_0 = 0$ and $F_1 = 1$. The number $4$ belongs to the set
$G = \{F_{3n}/2 : n \ge 1\} = \{1, 4, 17, 72, \dots\}$ of halves of the positive even Fibonacci
numbers; indeed $4 = F_6/2$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Section 2 (notation `G`, `g_n`). -/
theorem four_mem_halfEvenFibonacciSet : 4 ∈ halfEvenFibonacciSet :=
  ⟨1, by decide⟩

namespace not_accessible_four_of_halfEvenFibonacci

/-- An even Fibonacci number has an index divisible by three. -/
private theorem three_dvd_of_two_dvd_fib : ∀ {n : ℕ}, 2 ∣ Nat.fib n → 3 ∣ n
  | 0, _ => dvd_zero 3
  | 1, h => absurd h (by decide)
  | 2, h => absurd h (by decide)
  | n + 3, h => by
    have h₁ : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    have h₂ : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have := three_dvd_of_two_dvd_fib (n := n) (by omega)
    omega

/-- Every element of the halved set is positive. -/
private theorem subset_Ioi : halfEvenFibonacciSet ⊆ Set.Ioi 0 := by
  rintro _ ⟨n, rfl⟩
  exact Nat.div_pos ((by decide : 2 ≤ Nat.fib 3).trans (Nat.fib_mono (by omega))) two_pos

/-- Half of an even positive Fibonacci number lies in the halved set. -/
private theorem half_mem {n : ℕ} (hn : 2 ≤ n) (h : 2 ∣ Nat.fib n) :
    Nat.fib n / 2 ∈ halfEvenFibonacciSet := by
  obtain ⟨m, rfl⟩ := three_dvd_of_two_dvd_fib h
  obtain _ | m := m
  · omega
  · exact ⟨m, rfl⟩

/-- The positive integer $\lceil n/2 \rceil = (n + 1)/2$. -/
private def half (n : ℕ+) : ℕ+ :=
  ⟨((n : ℕ) + 1) / 2, by have := n.pos; omega⟩

end not_accessible_four_of_halfEvenFibonacci

open not_accessible_four_of_halfEvenFibonacci in
/-- **Halved even Fibonacci numbers and $4$-accessibility of the Fibonacci numbers.** Write $f_n$
for the $n$-th Fibonacci number ($f_0 = 0$, $f_1 = 1$). Let $F = \{1, 2, 3, 5, 8, \dots\}$ be the
set of positive Fibonacci numbers and $G = \{f_{3n}/2 : n \ge 1\} = \{1, 4, 17, 72, \dots\}$ the set
of halves of the even Fibonacci numbers. If $G$ is not $2$-accessible, then $F$ is not
$4$-accessible.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 3 (`integers-2025-A29-lem-3`). -/
public theorem not_accessible_four_of_halfEvenFibonacci
    (h : ¬ IsRAccessible 2 halfEvenFibonacciSet) :
    ¬ IsRAccessible 4 positiveFibonacciSet := by
  intro hF
  -- Refining a coloring by parity, the even positive Fibonacci numbers are `2`-accessible.
  obtain ⟨-, -, hE⟩ := accessible_divisible_subset positiveFibonacciSet 2 2 two_pos hF
  refine h ⟨subset_Ioi, one_le_two, fun χ k hk => ?_⟩
  -- Color `n` by the color of `⌈n / 2⌉`, then halve the terms of a monochromatic sequence.
  obtain ⟨x, hx, hdiff⟩ := hE (fun n => χ (half n)) k hk
  refine ⟨fun i => half (x i), hx, fun i hi => ?_⟩
  obtain ⟨d, ⟨⟨n, hn, rfl⟩, hd⟩, hgap⟩ := hdiff i hi
  refine ⟨Nat.fib n / 2, half_mem hn (Nat.dvd_of_mod_eq_zero hd), ?_⟩
  simp only [half, PNat.mk_coe] at hgap ⊢
  omega

end

end MetaMathlibExt
