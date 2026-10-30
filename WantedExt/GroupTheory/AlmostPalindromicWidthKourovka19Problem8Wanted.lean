/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Almost-palindromic width of the free group of rank two (Kourovka Notebook Problem 19.8)

Kourovka Notebook, Problem 19.8 (V. G. Bardakov), marked solved in the 21st issue: a word is an
almost `k`-palindrome if changing at most `k` letters turns it into a palindrome. With elements of
`F₂ = ⟨x, y⟩` represented by words in `x^{±1}, y^{±1}`, do there exist positive integers `m` and `c`
such that every element of `F₂` is a product of at most `c` almost `m`-palindromes?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.AlmostPalindromicWidthKourovka19Problem8Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.8 (V. G. Bardakov). UnsolvedMath record
UM-00701556 (`KOU-19.8`), dataset ulamai/UnsolvedMath v1.8.0.

Words are lists of letters `(i, b)` (`i : Fin 2`, `b = false` for an inverse letter), not
necessarily reduced, as in Staiger's paper, and represent elements via `FreeGroup.mk`. Allowing
unreduced words gives more almost palindromes than reduced words do, so the refutation also covers
the reduced reading.
-/

/-- A word `w` in the letters `x^{±1}, y^{±1}` (a list of pairs `(i, b)` with `i : Fin 2`, the
letter being inverted when `b = false`) is an almost `m`-palindrome: it differs from a palindrome
of the same length in at most `m` positions. The word need not be reduced. -/
def IsAlmostPalindrome (m : ℕ) (w : List (Fin 2 × Bool)) : Prop :=
  ∃ p : List (Fin 2 × Bool), p.length = w.length ∧ p.reverse = p ∧
    (List.zip w p).countP (fun q => q.1 ≠ q.2) ≤ m

/-- Kourovka 19.8 (V. G. Bardakov): there are positive integers `m` and `c` such that every element
of the free group `F₂ = ⟨x, y⟩` is a product of at most `c` almost `m`-palindromes. -/
def almostPalindromicWidthFinite : Prop :=
  ∃ m c : ℕ, 0 < m ∧ 0 < c ∧ ∀ g : FreeGroup (Fin 2), ∃ ws : List (List (Fin 2 × Bool)),
    ws.length ≤ c ∧ (∀ w ∈ ws, IsAlmostPalindrome m w) ∧ (ws.map FreeGroup.mk).prod = g

/--
Resolved false: Staiger (Theorem 1) proves that for every `m ≥ 0` the `m`-almost-palindromic width
of a non-abelian free group is infinite, so no `c` works; the 21st issue of the Kourovka Notebook
marks 19.8 solved ("No, there are no such integers"). Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Problem 19.8 (V. G. Bardakov); resolution: M. Staiger, On the almost-palindromic width of
free groups, J. Algebra 659 (2024), 475-481 (arXiv:2306.15752), Section 1: m-almost-palindromes are
words of the free monoid on the letters x^{±1}, y^{±1} (not necessarily reduced) within Hamming
distance m of a palindrome, and the width is taken for the group elements they represent; Theorem 1:
for a non-abelian free group F and every m ≥ 0 the m-almost-palindromic width of F is infinite; the
Kourovka Notebook (21st issue) marks 19.8 solved: No, there are no such integers,
https://arxiv.org/abs/2306.15752.
-/
public theorem_wanted almostPalindromicWidthFinite_refuted : ¬ almostPalindromicWidthFinite

end MathlibExt.GroupTheory.AlmostPalindromicWidthKourovka19Problem8Wanted
