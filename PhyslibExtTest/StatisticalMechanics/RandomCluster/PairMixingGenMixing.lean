/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PairMixingGenMixing

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PairMixingGenMixing`

On `ConfigSpace ℕ` with `Equiv.Perm ℕ` acting on sites:
* the Dirac measure at the all-open configuration satisfies `fmu_PairMixing` (an explicit witness:
  every multi-open event has mass `1`), so the hypothesis is satisfiable;
* `fmu_genMixing_of_pairMixing` then gives general mixing for it.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PairMixingGenMixing

open _root_.StatMech _root_.StatMech.FK MeasureTheory

/-- The Dirac measure at the all-open configuration of `ℕ`. -/
noncomputable def δ : Measure (ConfigSpace ℕ) := Measure.dirac (fun _ => true)

/-- `δ` is a probability measure. -/
instance : IsProbabilityMeasure δ := by unfold δ; infer_instance

/-- Every set containing the all-open configuration has `δ`-mass one. -/
theorem δ_real_of_mem {s : Set (ConfigSpace ℕ)} (h : (fun _ => true) ∈ s) : δ.real s = 1 := by
  simp [Measure.real, δ, Measure.dirac_apply_of_mem h]

/-- `δ` is pair mixing. -/
theorem δ_pairMixing : fmu_PairMixing (G := Equiv.Perm ℕ) δ := by
  intro P ε hε
  refine ⟨1, fun T _ T' _ => ?_⟩
  rw [δ_real_of_mem (s := fmu_multiOpen T ∩ ConfigSpace.shift 1 ⁻¹' fmu_multiOpen T')
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩,
    δ_real_of_mem (s := fmu_multiOpen T) fun _ _ => rfl,
    δ_real_of_mem (s := fmu_multiOpen T') fun _ _ => rfl]
  norm_num [hε]

-- Pair mixing implies general mixing.
example : fmu_GenMixing (G := Equiv.Perm ℕ) δ := fmu_genMixing_of_pairMixing δ_pairMixing

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PairMixingGenMixing
