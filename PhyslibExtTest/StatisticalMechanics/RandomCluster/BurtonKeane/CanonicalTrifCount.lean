/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalTrifCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalTrifCount`

* `ctc2_isCanonicalTrifurcation_threeRay` with `ctc2_isTrifurcation_of_canonical`: an explicit
  trifurcation exists;
* `CtcWitness.cut_disconnect_pos_neg`: the two horizontal arms separate at the hub;
* `ctc2_canonTcount_le_Tcount` for the all-open configuration;
* `ctc2_count_of_subsingleton` for the all-closed configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalTrifCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

/-- The all-closed configuration has no trifurcation. -/
theorem noTrif_closed {d : ℕ} (x : Site d) : ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a₁, a₂, -, ⟨h₁₂, -, -⟩, ⟨c₁, c₂, -⟩, -⟩
  have hbot : openSubgraph d (fun _ => false) = ⊥ := by
    ext u v; simp
  unfold Connected at c₁ c₂
  rw [hbot, SimpleGraph.reachable_bot] at c₁ c₂
  exact h₁₂ (c₁.symm.trans c₂)

-- Canonical trifurcations exist, hence trifurcations exist.
example : ∃ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2), IsTrifurcation 2 ω x :=
  let ⟨ω, x, h⟩ := ctc2_isCanonicalTrifurcation_threeRay
  ⟨ω, x, ctc2_isTrifurcation_of_canonical h⟩

-- The horizontal arms of the three-ray configuration separate at the hub.
example : ¬ Connected 2 (removeSite (CtcWitness.px 0) CtcWitness.threeRayConfig)
    (CtcWitness.px 1) (CtcWitness.px (-1)) :=
  CtcWitness.cut_disconnect_pos_neg

-- The canonical count is at most the count (all-open configuration).
example : ctc2_canonTcount 2 (fun _ => true) 3 ≤ Tcount 2 (fun _ => true) 3 :=
  ctc2_canonTcount_le_Tcount _ 3

-- The count bound for the all-closed configuration.
example : Tcount 2 (fun _ => false) 1 ≤ boxSV_boundaryCard 2 1 :=
  ctc2_count_of_subsingleton _ 1 le_rfl fun x _ _ hx => (noTrif_closed x hx).elim

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalTrifCount
