/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Infinite periodic groups with a finite maximal subgroup (Kourovka Notebook Problem 3.9)

Kourovka Notebook, Archive of Solved Problems, Problem 3.9 (Yu. M. Gorchakov): does there exist an
infinite periodic group with a finite maximal subgroup?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Order.Atoms

@[expose] public section

namespace MathlibExt.GroupTheory.PeriodicGroupFiniteMaximalSubgroupKourovka3Problem9Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.9 (Yu. M.
Gorchakov). UnsolvedMath record UM-00700163 (`KOU-3.9`), dataset ulamai/UnsolvedMath v1.8.0.

Periodic means every element has finite order; a maximal subgroup is a coatom of the subgroup
lattice (`IsCoatom`). No locally finite group witnesses the statement: if `M` is a finite maximal
subgroup and `g ∉ M`, then `⟨M, g⟩ = G` is finitely generated, hence finite.
-/

/-- Kourovka 3.9 (Yu. M. Gorchakov): there is an infinite periodic group (every element has finite
order) with a finite maximal subgroup. -/
def existsInfinitePeriodicGroupFiniteMaximalSubgroup : Prop :=
  ∃ (G : Type) (_ : Group G), Infinite G ∧ (∀ g : G, IsOfFinOrder g) ∧
    ∃ M : Subgroup G, IsCoatom M ∧ Finite M

/--
Resolved true: Adian (1971) constructed an infinite periodic group with a finite maximal subgroup;
the Kourovka Archive answers 3.9 "Yes, there does". Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 3.9 (Yu. M. Gorchakov); resolution: S. I. Adian, On subgroups of
free periodic groups of odd exponent, Proc. Steklov Inst. Math. 112 (1971), 61-69, Kourovka Archive
of Solved Problems, Problem 3.9: Yes, there does, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted existsInfinitePeriodicGroupFiniteMaximalSubgroup_holds :
    existsInfinitePeriodicGroupFiniteMaximalSubgroup

end MathlibExt.GroupTheory.PeriodicGroupFiniteMaximalSubgroupKourovka3Problem9Wanted
