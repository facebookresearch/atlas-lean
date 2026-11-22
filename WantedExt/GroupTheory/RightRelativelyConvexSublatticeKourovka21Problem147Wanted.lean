/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Right-relatively convex subgroups and the subgroup lattice (Kourovka Notebook Problem 21.147)

Kourovka Notebook, Problem 21.147 (V. M. Kopytov, N. Ya. Medvedev; A. V. Zenkov), marked solved in
the 21st issue: a subgroup `H` of a right-orderable group `G` is said to be right-relatively convex
if it is convex under some right ordering on `G`. Is the lattice of right-relatively convex
subgroups of a right-orderable group always a sublattice of the lattice of its subgroups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import WantedExt.GroupTheory.ResiduallyTwoPrimesNotRightOrderableKourovka10Problem30Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.RightRelativelyConvexSublatticeKourovka21Problem147Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.147 (V. M. Kopytov, N. Ya. Medvedev; A.
V. Zenkov). UnsolvedMath record UM-00002656 (`KOU-21.147`), dataset ulamai/UnsolvedMath v1.8.0.

A right ordering is a linear order `o` on `G` with `a ≤ b → a c ≤ b c`; `H` is convex for `o` when
`h₁ ≤ g ≤ h₂` with `h₁, h₂ ∈ H` forces `g ∈ H` (`IsRightOrderable` of the Kourovka 10.30 entry,
reused here, and `IsRightRelativelyConvex`).
Being a sublattice of the subgroup lattice means being closed under `⊓` (intersection) and `⊔`
(generated subgroup). The group is required to be non-abelian: van Doorn, Judin, Monticone and
Morrison (Appendix A) report that an abelian counterexample was already known and that the proposers
meant to ask about non-abelian groups. A refutation of this form also refutes the question as
printed.
-/

open MathlibExt.GroupTheory.ResiduallyTwoPrimesNotRightOrderableKourovka10Problem30Wanted
  (IsRightOrderable)

/-- The linear order `o` on `G` is a right order: `a ≤ b` implies `a c ≤ b c`. -/
def IsRightInvariantOrder {G : Type} [Group G] (o : LinearOrder G) : Prop :=
  ∀ a b : G, o.le a b → ∀ c : G, o.le (a * c) (b * c)

/-- `H` is right-relatively convex in `G`: convex for some right order `o` of `G`, that is,
`h₁ ≤ g ≤ h₂` with `h₁, h₂ ∈ H` implies `g ∈ H`. -/
def IsRightRelativelyConvex {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∃ o : LinearOrder G, IsRightInvariantOrder o ∧
    ∀ h₁ ∈ H, ∀ h₂ ∈ H, ∀ g : G, o.le h₁ g → o.le g h₂ → g ∈ H

/-- Kourovka 21.147 (V. M. Kopytov, N. Ya. Medvedev), for non-abelian groups as the proposers
meant: in every non-abelian right-orderable group the right-relatively convex subgroups form a
sublattice of the subgroup lattice, i.e. they are closed under intersection and under the join (the
generated subgroup). -/
def rightRelativelyConvexSublattice : Prop :=
  ∀ (G : Type) [Group G], (∃ a b : G, a * b ≠ b * a) → IsRightOrderable G → ∀ H K : Subgroup G,
    IsRightRelativelyConvex H → IsRightRelativelyConvex K →
      IsRightRelativelyConvex (H ⊓ K) ∧ IsRightRelativelyConvex (H ⊔ K)

/--
Resolved false: in the integer Heisenberg group, which is non-abelian, the cyclic subgroups `⟨(1, 0,
1)⟩` and `⟨(1, 0, -1)⟩` are convex for suitable right orders, but the subgroup `J` they generate
contains `2e` and not `e = (1, 0, 0)`, and every right order puts `e` between `0` and `2e`, so `J`
is convex for no right order (van Doorn, Judin, Monticone and Morrison, Theorem 8.1; Monticone's
note). The 21st issue of the Kourovka Notebook marks 21.147 solved ("No, not always"; AI solution
confirmed by A. V. Zenkov). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.147 (V. M.
Kopytov, N. Ya. Medvedev; A. V. Zenkov); resolution: P. Monticone, Kourovka Notebook Problem 21.147,
solution note (14 May 2026), Kourovka Notebook site; W. van Doorn, E. Judin, P. Monticone and D.
Morrison, On some problems from the Kourovka Notebook, preprint, arXiv:2607.17477 (2026), van
Doorn-Judin-Monticone-Morrison, Theorem 8.1: in the integer Heisenberg group the subgroups ⟨(1, 0,
1)⟩ and ⟨(1, 0, -1)⟩ are right-relatively convex, while their join contains 2e but not e = (1, 0, 0)
and so is not convex for any right order; an AI solution (Aristotle) confirmed by A. V. Zenkov,
Kourovka Notebook (21st issue), Problem 21.147: No, not always, https://arxiv.org/abs/2607.17477.
-/
public theorem_wanted rightRelativelyConvexSublattice_refuted : ¬ rightRelativelyConvexSublattice

end MathlibExt.GroupTheory.RightRelativelyConvexSublatticeKourovka21Problem147Wanted
