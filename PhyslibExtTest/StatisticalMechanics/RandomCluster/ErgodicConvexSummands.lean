/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.ErgodicConvexSummands

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.ErgodicConvexSummands`

On `ConfigSpace ℕ` with the permutation group `Equiv.Perm ℕ` acting on sites, the Dirac measure at
the all-open configuration:
* is ergodic (an explicit `IsErgodic` witness, so the hypothesis is satisfiable);
* `ergodic_invariant_event_zero_or_one` for the invariant event `univ`;
* `le_self_of_convexCombo` and `ergodic_summands_eq_on_invariants` for its trivial decomposition
  `δ = ½ δ + ½ δ`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.ErgodicConvexSummands

open _root_.StatMech _root_.StatMech.FK MeasureTheory

/-- The Dirac measure at the all-open configuration of `ℕ`. -/
noncomputable def δ : Measure (ConfigSpace ℕ) := Measure.dirac (fun _ => true)

/-- `δ` is a probability measure. -/
instance : IsProbabilityMeasure δ := by unfold δ; infer_instance

/-- Shifts by permutations are measurable. -/
theorem shift_meas (g : Equiv.Perm ℕ) : Measurable (ConfigSpace.shift (E := ℕ) g) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-- The Dirac measure at a constant configuration is ergodic. -/
theorem δ_ergodic : ConfigSpace.IsErgodic (G := Equiv.Perm ℕ) δ := by
  refine ⟨fun g => ⟨shift_meas g, ?_⟩, fun s hs _ => ?_⟩
  · rw [δ, Measure.map_dirac' (shift_meas g)]
    rfl
  · rw [δ, Measure.dirac_apply' _ hs, Measure.dirac_apply' _ MeasurableSet.univ]
    by_cases h : (fun _ => true) ∈ s <;> simp [h]

/-- `δ` is the half-half convex combination of itself. -/
theorem δ_conv : δ = (2⁻¹ : ENNReal) • δ + (2⁻¹ : ENNReal) • δ := by
  rw [← add_smul, ENNReal.inv_two_add_inv_two, one_smul]

-- Invariant events have mass `0` or `1`.
example : δ Set.univ = 0 ∨ δ Set.univ = 1 :=
  ergodic_invariant_event_zero_or_one δ_ergodic MeasurableSet.univ fun _ => Set.preimage_univ

-- The convex summands are bounded by the measure.
example (s : Set (ConfigSpace ℕ)) : 2⁻¹ * δ s ≤ δ s ∧ 2⁻¹ * δ s ≤ δ s :=
  le_self_of_convexCombo δ_conv s

-- The convex summands agree on invariant events.
example : δ Set.univ = δ Set.univ :=
  ergodic_summands_eq_on_invariants δ_ergodic δ_conv (by norm_num) (by norm_num)
    MeasurableSet.univ fun _ => Set.preimage_univ

end PhyslibExtTest.StatisticalMechanics.RandomCluster.ErgodicConvexSummands
