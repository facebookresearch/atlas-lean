/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely presented orderable groups with insoluble word problem (Kourovka Notebook Problem 17.29)

Kourovka Notebook, Archive of Solved Problems, Problem 17.29 (V. V. Bludov, A. M. W. Glass):
construct a finitely presented orderable group with insoluble word problem.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import WantedExt.GroupTheory.WordProblemSolvableShared

@[expose] public section

namespace MathlibExt.GroupTheory.FinitelyPresentedOrderableWordProblemKourovka17Problem29Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.29 (V. V.
Bludov, A. M. W. Glass). UnsolvedMath record UM-00701331 (`KOU-17.29`), dataset ulamai/UnsolvedMath
v1.8.0.

"Construct" is formalized as existence. Orderable means two-sided orderable: a linear order
invariant under left and right multiplication. Finitely presented is Mathlib's
`Group.IsFinitelyPresented`; the word problem for a finite generating family `gens : Fin k → G` is
the set of words spelling `1`, insoluble when not computable: the shared predicate
`WordProblemSolvable (FreeGroup.lift gens)` of `WantedExt.GroupTheory.WordProblemSolvableShared`
fails.
-/

open MathlibExt.GroupTheory.WordProblemSolvableShared

/-- The (two-sided) orders of `G`: linear orders (as relations) invariant under left and right
multiplication. -/
def biOrders (G : Type*) [Group G] : Set (G → G → Prop) :=
  {r | IsLinearOrder G r ∧ ∀ a b c : G, r a b → r (c * a) (c * b) ∧ r (a * c) (b * c)}

/-- Kourovka 17.29 (V. V. Bludov, A. M. W. Glass): there is a finitely presented orderable group
with insoluble word problem. -/
def finitelyPresentedOrderableInsolubleWordProblem : Prop :=
  ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ (biOrders G).Nonempty ∧
    ∃ (k : ℕ) (gens : Fin k → G), Subgroup.closure (Set.range gens) = ⊤ ∧
      ¬ WordProblemSolvable (FreeGroup.lift gens)

/--
Resolved true: the Kourovka Archive records for 17.29 "Such a group is constructed", citing Bludov
and Glass (2012): there is a finitely presented orderable group with insoluble word problem. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.29 (V. V. Bludov, A.
M. W. Glass); resolution: V. V. Bludov and A. M. W. Glass, Bull. London Math. Soc. 44 (2012), 85-98,
Kourovka Archive, Problem 17.29 (Such a group is constructed).
-/
public theorem_wanted finitelyPresentedOrderableInsolubleWordProblem_holds :
    finitelyPresentedOrderableInsolubleWordProblem

end MathlibExt.GroupTheory.FinitelyPresentedOrderableWordProblemKourovka17Problem29Wanted
