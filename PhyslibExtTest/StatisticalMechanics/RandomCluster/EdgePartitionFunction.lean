/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.EdgePartitionFunction

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.EdgeConfigZ`

* `ecz_box_edge_pos`: the box `Λ_1` of `ℤ²` has an edge;
* `ecz_fk_uniqueness` (uniqueness of the `q = 2` infinite-volume measure off a countable set) on
  `ℤ²`, box `Λ_1`, with the edge from `ecz_box_edge_pos`, and its consequence: some
  `t ∈ (0, 1)` gives agreement of the free and wired measures on every increasing event of `Λ_1`.
  (This replaces the smoke check removed from the source file in stage 3.)
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.EdgeConfigZ

open MeasureTheory _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

/-- The box `Λ_1` of `ℤ²` has an edge. -/
theorem box_edge_nonempty : (boxGraph 2 1).edgeFinset.Nonempty :=
  Finset.card_pos.mp (ecz_box_edge_pos 2 (by norm_num) (by norm_num))

/-- The `q = 2` disagreement set on `ℤ²`, box `Λ_1`, is countable. -/
theorem disagreement_countable :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts 2 1))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass 2 1 t) A ≠ eventMassProb (fuc_wiredMass 2 1 t) A}.Countable :=
  ecz_fk_uniqueness (d := 2) (by norm_num) 1 box_edge_nonempty.choose
    box_edge_nonempty.choose_spec

-- Consequence: some `t ∈ (0, 1)` gives agreement on every increasing event of `Λ_1`.
example : ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∀ A : Set (ConfigSpace (Sym2 (boxVerts 2 1))),
    IsIncreasing A →
      eventMassProb (fuc_freeMass 2 1 t) A = eventMassProb (fuc_wiredMass 2 1 t) A := by
  obtain ⟨t, ht, hbad⟩ := (disagreement_countable.dense_compl ℝ).inter_open_nonempty
    (Set.Ioo 0 1) isOpen_Ioo (Set.nonempty_Ioo.mpr (by norm_num))
  refine ⟨t, ht, fun A hA => ?_⟩
  by_contra hne
  exact hbad ⟨A, hA, hne⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.EdgeConfigZ
