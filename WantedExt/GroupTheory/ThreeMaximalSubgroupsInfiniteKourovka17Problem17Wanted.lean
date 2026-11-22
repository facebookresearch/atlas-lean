/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely generated groups with three maximal subgroups (Kourovka Notebook Problem 17.17)

Kourovka Notebook, Archive of Solved Problems, Problem 17.17 (G. M. Bergman): if a finitely
generated group `G` has `n < ∞` maximal subgroups, must `G` be finite? In particular, what if `n =
3`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Order.Atoms

@[expose] public section

namespace MathlibExt.GroupTheory.ThreeMaximalSubgroupsInfiniteKourovka17Problem17Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.17 (G. M.
Bergman). UnsolvedMath record UM-00701319 (`KOU-17.17`), dataset ulamai/UnsolvedMath v1.8.0.

Maximal subgroups are the coatoms of the subgroup lattice. The target is the case `n = 3` that the
problem singles out; its refutation also refutes the general question.
-/

/-- Kourovka 17.17 (G. M. Bergman), in the case `n = 3` singled out in the problem: every finitely
generated group with exactly three maximal subgroups is finite. -/
def threeMaximalSubgroupsFinite : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → {M : Subgroup G | IsCoatom M}.ncard = 3 → Finite G

/--
Resolved false: the Kourovka Archive answers 17.17 "No, it need not": a 2-generated 2-LERF group
constructed in Section 7 of Ershov and Jaikin-Zapirain (2013) is infinite and has exactly three
maximal subgroups, each of index 2. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 17.17 (G. M. Bergman); resolution: M. Ershov and A. Jaikin-Zapirain, J.
Reine Angew. Math. 677 (2013), 71-134, Kourovka Archive, Problem 17.17 (No, it need not: a
2-generated 2-LERF group in Section 7 of Ershov-Jaikin-Zapirain is an infinite group with 3 maximal
subgroups, all of index 2).
-/
public theorem_wanted threeMaximalSubgroupsFinite_refuted : ¬ threeMaximalSubgroupsFinite

end MathlibExt.GroupTheory.ThreeMaximalSubgroupsInfiniteKourovka17Problem17Wanted
