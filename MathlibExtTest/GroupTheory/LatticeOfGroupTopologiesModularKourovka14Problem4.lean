/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.LatticeOfGroupTopologiesModularKourovka14Problem4

/-! # Tests for the refutation of Kourovka Problem 14.4(b) -/

namespace MathlibExtTest.GroupTheory.LatticeOfGroupTopologiesModularKourovka14Problem4

open MathlibExt.GroupTheory.LatticeOfGroupTopologiesModularKourovka14Problem4Wanted
open scoped Topology

example : ¬ countableNilpotentNonabelianTopologyLatticeNotModular :=
  countableNilpotentNonabelianTopologyLatticeNotModular_refuted

-- The refutation provides a countably infinite non-abelian nilpotent group whose lattice of group
-- topologies is modular. This lattice is not a single point: on a group with more than one element
-- the discrete topology `⊥` and the indiscrete topology `⊤` differ.
example : ∃ (G : Type) (_ : Group G), Countable G ∧ Infinite G ∧ Group.IsNilpotent G ∧
    (∃ x y : G, x * y ≠ y * x) ∧ IsModularLattice (GroupTopology G) ∧
    (⊥ : GroupTopology G) ≠ ⊤ := by
  by_contra hne
  apply countableNilpotentNonabelianTopologyLatticeNotModular_refuted
  intro G _ hc hi hn hnc hmod
  have hbt : (⊥ : GroupTopology G) ≠ ⊤ := by
    intro h
    obtain ⟨x, y, hxy⟩ := exists_pair_ne G
    have hopen : IsOpen[(⊤ : GroupTopology G).toTopologicalSpace] ({x} : Set G) := by
      rw [← h, GroupTopology.toTopologicalSpace_bot]
      trivial
    rw [GroupTopology.toTopologicalSpace_top, TopologicalSpace.isOpen_top_iff] at hopen
    rcases hopen with hopen | hopen
    · exact Set.singleton_ne_empty x hopen
    · exact hxy ((Set.eq_univ_iff_forall.1 hopen y).symm)
  exact hne ⟨G, inferInstance, hc, hi, hn, hnc, hmod, hbt⟩

end MathlibExtTest.GroupTheory.LatticeOfGroupTopologiesModularKourovka14Problem4
