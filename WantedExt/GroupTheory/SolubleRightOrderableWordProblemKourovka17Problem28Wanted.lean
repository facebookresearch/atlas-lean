/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Soluble right-orderable groups with insoluble word problem (Kourovka Notebook Problem 17.28)

Kourovka Notebook, Archive of Solved Problems, Problem 17.28 (V. V. Bludov, A. M. W. Glass): is
there a soluble right-orderable group with insoluble word problem?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Solvable
public import WantedExt.GroupTheory.WordProblemSolvableShared

@[expose] public section

namespace MathlibExt.GroupTheory.SolubleRightOrderableWordProblemKourovka17Problem28Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.28 (V. V.
Bludov, A. M. W. Glass). UnsolvedMath record UM-00701330 (`KOU-17.28`), dataset ulamai/UnsolvedMath
v1.8.0.

The word problem is posed, as in the resolution, for finitely generated recursively presented
groups: for a finite generating family `gens : Fin k → G` it is the set of words (lists of letters
`(i, ε)`, `ε = false` for an inverse) that spell `1`. The group is recursively presented when this
set is recursively enumerable (`REPred`; for a finitely generated group this is the same as having a
presentation with a recursively enumerable set of relators), and the word problem is insoluble when
the set is not computable: the shared predicate `WordProblemSolvable (FreeGroup.lift gens)` of
`WantedExt.GroupTheory.WordProblemSolvableShared` (`ComputablePred` on Mathlib's `Primcodable`
coding of lists) fails. Neither property depends on the finite generating set. Soluble is
`Group.IsSolvable`; right orders are linear orders (as relations) invariant under right
multiplication.
-/

open MathlibExt.GroupTheory.WordProblemSolvableShared

/-- **Recursively presented group.** Let $G$ be a group, $k$ a natural number and $\varphi$ a
homomorphism from the free group on $k$ generators to $G$. The group $G$ is recursively presented
with respect to $\varphi$ when the set of words $w$ (finite lists of letters $(i, \varepsilon)$
with $i < k$ and $\varepsilon$ true or false, the letter $(i, \mathrm{false})$ standing for the
inverse of the $i$-th generator) with $\varphi(w) = 1$ in $G$ is recursively enumerable.

When $\varphi$ is surjective, this is the same as a presentation of $G$ on the images of the
generators with a recursively enumerable set of relators; it is the enumerable counterpart of a
solvable word problem. -/
def IsRecursivelyPresented {G : Type*} [Group G] {k : ℕ} (φ : FreeGroup (Fin k) →* G) : Prop :=
  REPred (fun w : List (Fin k × Bool) => φ (FreeGroup.mk w) = 1)

/-- The right orders of `G`: linear orders (as relations) invariant under right multiplication. -/
def rightOrders (G : Type*) [Group G] : Set (G → G → Prop) :=
  {r | IsLinearOrder G r ∧ ∀ a b c : G, r a b → r (a * c) (b * c)}

/-- **The Bludov–Glass question (Kourovka 17.28).** The statement that there exist a soluble group
$G$ that admits a right order, a natural number $k$ and elements $g_0, \dots, g_{k-1}$ generating
$G$ such that, for the homomorphism $\varphi$ from the free group on $k$ generators to $G$ sending
the $i$-th generator to $g_i$, the group $G$ is recursively presented with respect to $\varphi$
and the word problem for $\varphi$ is not solvable. In words: there is a finitely generated,
recursively presented, soluble right-orderable group with insoluble word problem. -/
def solubleRightOrderableInsolubleWordProblem : Prop :=
  ∃ (G : Type) (_ : Group G), Group.IsSolvable G ∧ (rightOrders G).Nonempty ∧
    ∃ (k : ℕ) (gens : Fin k → G), Subgroup.closure (Set.range gens) = ⊤ ∧
      IsRecursivelyPresented (FreeGroup.lift gens) ∧ ¬ WordProblemSolvable (FreeGroup.lift gens)

/--
**A soluble right-orderable group with insoluble word problem (Kourovka 17.28).** There exist a
soluble group $G$ that admits a right order, a natural number $k$ and elements
$g_0, \dots, g_{k-1}$ generating $G$ such that, for the homomorphism $\varphi$ from the free group
on $k$ generators to $G$ sending the $i$-th generator to $g_i$, the group $G$ is recursively
presented with respect to $\varphi$ and the word problem for $\varphi$ is not solvable.

Resolved true: Darbinyan constructs a two-generated, recursively presented, bi-orderable (hence
right-orderable) soluble group of derived length 3 with undecidable word problem; the Kourovka
Archive answers 17.28 "Yes, there is".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 17.28 (V. V. Bludov, A. M. W. Glass); resolution: A. Darbinyan,
Computability, orders, and solvable groups, J. Symbolic Logic 85 (2020), 1588-1598
(arXiv:1909.05720), abstract, result (2) (a bi-orderable, two-generated, recursively presented
solvable group of derived length 3 with undecidable word problem, answering the question of Bludov
and Glass); Kourovka Archive, Problem 17.28 (Yes, there is), https://arxiv.org/abs/1909.05720.
-/
public theorem_wanted solubleRightOrderableInsolubleWordProblem_holds :
    solubleRightOrderableInsolubleWordProblem

end MathlibExt.GroupTheory.SolubleRightOrderableWordProblemKourovka17Problem28Wanted
