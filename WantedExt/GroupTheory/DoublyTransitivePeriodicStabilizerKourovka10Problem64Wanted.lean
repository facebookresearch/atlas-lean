/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Doubly transitive groups with periodic point stabilizers (Kourovka Notebook Problem 10.64)

Kourovka Notebook, Problem 10.64 (Ya. P. Sysak), marked solved: does there exist a non-periodic
doubly transitive permutation group with a periodic stabilizer of a point?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

@[expose] public section

namespace MathlibExt.GroupTheory.DoublyTransitivePeriodicStabilizerKourovka10Problem64Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 10.64 (Ya. P. Sysak). UnsolvedMath record
UM-00700679 (`KOU-10.64`), dataset ulamai/UnsolvedMath v1.8.0.

A permutation group is a faithful action; doubly transitive is `MulAction.IsMultiplyPretransitive G
X 2`; periodic means that every element has finite order. All point stabilizers are conjugate, so
one of them suffices.
-/

/-- Kourovka 10.64 (Ya. P. Sysak): some non-periodic doubly transitive permutation group (a faithful
`2`-transitive action) has a periodic point stabilizer. -/
def doublyTransitiveNonperiodicPeriodicStabilizer : Prop :=
  ∃ (G X : Type) (_ : Group G) (_ : MulAction G X), FaithfulSMul G X ∧
    MulAction.IsMultiplyPretransitive G X 2 ∧ (∃ g : G, ¬ IsOfFinOrder g) ∧
    ∃ x : X, ∀ h ∈ MulAction.stabilizer G x, IsOfFinOrder h

/--
Resolved true: Amelio (arXiv:2509.11958, Theorem 1.3, restated as Theorem 3.5) constructs a
non-periodic non-split sharply `2`-transitive group in which the centralizer of every involution has
bounded exponent; by Section 3.2 these centralizers are the point stabilizers of the action on the
involutions, so this answers the paper's Question 2 (Kourovka 10.64) positively. The Kourovka
Notebook (21st issue) marks 10.64 solved, "Yes, it does exist". Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Problem 10.64 (Ya. P. Sysak); resolution: M. Amelio, Non-split sharply
2-transitive groups of bounded exponent, arXiv:2509.11958 (2025), Theorem 1.3 (restated as Theorem
3.5) and Section 3.2: a non-periodic non-split sharply 2-transitive group whose involution
centralizers, the point stabilizers of its action on the involutions, have bounded exponent, a
positive answer to the paper's Question 2 (Kourovka 10.64); the Kourovka Notebook (21st issue) marks
10.64 solved, https://arxiv.org/abs/2509.11958.
-/
public theorem_wanted doublyTransitiveNonperiodicPeriodicStabilizer_holds :
    doublyTransitiveNonperiodicPeriodicStabilizer

end MathlibExt.GroupTheory.DoublyTransitivePeriodicStabilizerKourovka10Problem64Wanted
