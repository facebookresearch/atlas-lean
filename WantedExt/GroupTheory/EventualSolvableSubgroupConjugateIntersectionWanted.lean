/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Batteries.Util.ProofWanted

@[expose] public section

/-!
# Eventual trivial intersections of conjugated solvable subgroups

The eventual part of Kourovka Notebook Problem 21.3 asks whether, for all sufficiently large `n`,
every pair of solvable subgroups of `Sₙ` or `Aₙ` has conjugates with trivial intersection.
-/

namespace MathlibExt.GroupTheory.EventualSolvableSubgroupConjugateIntersectionWanted

/-- The right-conjugate `K ^ x = x⁻¹ K x`. -/
def conjugateSubgroup {G : Type} [Group G] (K : Subgroup G) (x : G) : Subgroup G :=
  K.map (MulAut.conj (x⁻¹))

/-- Every pair of solvable subgroups has a conjugate pair with trivial intersection. -/
def SolvableSubgroupsHaveDisjointConjugates (G : Type) [Group G] : Prop :=
  ∀ H K : Subgroup G,
    Group.IsSolvable H → Group.IsSolvable K →
      ∃ x : G, H ⊓ conjugateSubgroup K x = ⊥

/-- For all sufficiently large `n`, the solvable-subgroup conjugate-intersection property holds in
both `Sₙ` and `Aₙ`. -/
def conjecture : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    SolvableSubgroupsHaveDisjointConjugates (Equiv.Perm (Fin n)) ∧
      SolvableSubgroupsHaveDisjointConjugates (alternatingGroup (Fin n))

/--
Resolved true: Answered affirmatively: A. Rizzoli (preprint, 2026), Corollary 4.1, proves that
there is N such that for every n ≥ N and G = S_n or A_n, every pair of soluble subgroups H, K ≤
G admits x ∈ G with H ∩ x⁻¹Kx = 1. The Kourovka Notebook (arXiv:1401.0300v49) marks part a) of
Problem 21.3 solved with this reference; part b), the threshold n ≥ 21, remains open. Source: A.
Rizzoli, The soluble-intersection limit in S_n (preprint, 2026, Kourovka Notebook site),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_21_3a.pdf; E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (20 October 2026), Problem 21.3, https://arxiv.org/abs/1401.0300v49.
Moved from `OpenConjectures/GroupTheory/EventualSolvableSubgroupConjugateIntersection`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GroupTheory.EventualSolvableSubgroupConjugateIntersectionWanted
