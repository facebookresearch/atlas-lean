/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite groups with exactly one non-commutator (Kourovka Notebook Problem 17.76)

Kourovka Notebook, Problem 17.76 (D. MacHale): does there exist a finite group `G`, with `|G| > 2`,
such that there is exactly one element in `G` which is not a commutator?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.GroupTheory.ExactlyOneNoncommutatorKourovka17Problem76Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.76 (D. MacHale). UnsolvedMath record
UM-00701378 (`KOU-17.76`), dataset ulamai/UnsolvedMath v1.8.0.

A commutator is an element `x⁻¹ y⁻¹ x y`; the target asks for a finite group of order greater than
`2` whose set of non-commutators has exactly one element (`Set.ncard`).
-/

/-- **Kourovka Problem 17.76 (finite groups with exactly one non-commutator).** This is the
statement that there is a finite group $G$ of order greater than $2$ in which exactly one element is
not a commutator, that is, not of the form $x^{-1}y^{-1}xy$ with $x, y \in G$. -/
def exactlyOneNoncommutator : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), 2 < Nat.card G ∧
    {g : G | ¬ ∃ x y : G, g = x⁻¹ * y⁻¹ * x * y}.ncard = 1

/--
**A finite group with exactly one non-commutator.** There is a finite group $G$ of order greater
than $2$ in which exactly one element is not a commutator, that is, not of the form $x^{-1}y^{-1}xy$
with $x, y \in G$.

Resolved true: Skresanov constructs an infinite series of finite groups with exactly one element
that is not a commutator, the smallest of order 16609443840, and Hatem and Siniora find two such
groups of order 368640, the smallest possible order. The Kourovka Notebook (21st issue) answers
17.76 "Yes".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.76 (D. MacHale); resolution: S.
V. Skresanov, Siberian Electron. Math. Rep. 23 (2026), 603-607 (preprint On finite groups with
exactly one noncommutator, arXiv:2509.17587); O. Hatem and D. Siniora, Int. J. Group Theory 15
(2026), 161-167 (preprint A group with exactly one noncommutator, arXiv:2511.00541), Skresanov,
abstract (an infinite series of such groups, the smallest of order 16609443840); Hatem-Siniora,
abstract (two non-isomorphic groups of order 368640, the smallest order); the Kourovka Notebook
(21st issue) marks 17.76 solved (Yes, such groups do exist, and there are infinitely many examples),
https://arxiv.org/abs/2509.17587.
-/
public theorem_wanted exactlyOneNoncommutator_holds : exactlyOneNoncommutator

end MathlibExt.GroupTheory.ExactlyOneNoncommutatorKourovka17Problem76Wanted
