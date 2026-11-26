/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalTrifCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalTrifCount`

* `bc48_fakeConfig_classical_proper_subset`: classical trifurcations are a proper subset on the
  fake configuration;
* `bc48_Tcount_classical_eq_zero_of_noTrif` and `bc48_classicalInjection_of_noTrif` for the
  all-closed configuration;
* `bc48_measurableSet_isClassicalTrifurcation` at the origin of `ℤ²`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalTrifCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

/-- The all-closed configuration has no trifurcation. -/
theorem noTrif_closed {d : ℕ} (x : Site d) : ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a₁, a₂, -, ⟨h₁₂, -, -⟩, ⟨c₁, c₂, -⟩, -⟩
  have hbot : openSubgraph d (fun _ => false) = ⊥ := by
    ext u v; simp
  unfold Connected at c₁ c₂
  rw [hbot, SimpleGraph.reachable_bot] at c₁ c₂
  exact h₁₂ (c₁.symm.trans c₂)

-- Classical trifurcations form a proper subset on the fake configuration.
example : bc48_classicalTrifFinset bc47_fakeConfig 2 ⊂ tfc_trifFinset bc47_fakeConfig 2 :=
  bc48_fakeConfig_classical_proper_subset 2

-- No classical trifurcation in the all-closed configuration.
example : bc48_Tcount_classical 2 (fun _ => false) 3 = 0 :=
  bc48_Tcount_classical_eq_zero_of_noTrif _ 3 fun x _ => noTrif_closed x
example : bc48_ClassicalBoundaryArmInjection (d := 2) (fun _ => false) 3 :=
  bc48_classicalInjection_of_noTrif _ 3 fun x _ => noTrif_closed x

-- Classical trifurcation at the origin is measurable.
example : MeasurableSet {ω : ConfigSpace (Sym2 (Site 2)) | bc47_IsClassicalTrifurcation ω 0} :=
  bc48_measurableSet_isClassicalTrifurcation 0

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalTrifCount
