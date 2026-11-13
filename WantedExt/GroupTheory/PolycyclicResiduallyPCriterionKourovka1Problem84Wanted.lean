/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Polycyclic residually finite `p`-groups (Kourovka Notebook Problem 1.84)

Kourovka Notebook, Archive of Solved Problems, Problem 1.84 (A. L. Shmel'kin): is it true that a
polycyclic group `G` is residually a finite `p`-group if and only if `G` has a nilpotent normal
torsion-free subgroup of `p`-power index?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Nilpotent
public import WantedExt.GroupTheory.GroupClassesShared
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.GroupTheory.PolycyclicResiduallyPCriterionKourovka1Problem84Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.84 (A. L.
Shmel'kin). UnsolvedMath record UM-00700073 (`KOU-1.84`), dataset ulamai/UnsolvedMath v1.8.0.

Polycyclic is `IsPolycyclic` of `GroupClassesShared`: a finite subnormal series with cyclic factors
(by Hirsch's theorem, equivalently soluble with every subgroup finitely generated). Residually a
finite `p`-group means that every element `≠ 1` lies outside a normal subgroup of `p`-power index.
The prime `p` is universally quantified, so the refutation says that the equivalence fails for some
prime and some polycyclic group.
-/

open MathlibExt.GroupTheory.GroupClassesShared (IsPolycyclic)
open MathlibExt.GroupTheory.KourovkaNotebookShared (IsResiduallyFiniteP)

/-- `G` has a torsion-free nilpotent normal subgroup whose index is a power of `p`. -/
def HasTorsionFreeNilpotentNormalPPowerIndex (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ N : Subgroup G, N.Normal ∧ (∃ k : ℕ, N.index = p ^ k) ∧ Group.IsNilpotent N ∧
    ∀ x : N, x ≠ 1 → ¬ IsOfFinOrder x

/-- Kourovka 1.84 (A. L. Shmel'kin): for every prime `p`, a polycyclic group is residually a finite
`p`-group if and only if it has a torsion-free nilpotent normal subgroup of `p`-power index. -/
def polycyclicResiduallyPCriterion : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G], IsPolycyclic G →
    (IsResiduallyFiniteP p G ↔ HasTorsionFreeNilpotentNormalPPowerIndex p G)

/--
Resolved false: the Kourovka Archive answers 1.84 "No, it is not", citing Seksenbaev (1965): for
some prime `p` and some polycyclic group the two conditions are not equivalent. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.84 (A. L. Shmel'kin);
resolution: K. Seksenbaev, Algebra i Logika 4, no. 3 (1965), 79-83 (Russian), Kourovka Archive,
Problem 1.84 ("No, it is not").
-/
public theorem_wanted polycyclicResiduallyPCriterion_refuted : ¬ polycyclicResiduallyPCriterion

end MathlibExt.GroupTheory.PolycyclicResiduallyPCriterionKourovka1Problem84Wanted
