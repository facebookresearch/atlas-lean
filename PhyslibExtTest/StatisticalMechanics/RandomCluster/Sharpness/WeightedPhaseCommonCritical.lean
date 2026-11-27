/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedPhaseCommonCritical

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedPhaseCommonCritical`

For the homogeneous coupling on `ℤ²` with the two-phase labelling "first coordinate is `0`"
(a surjective, phase-covariant labelling), `q = 2`:
* `covariantWeightedPhasePositivityTransport`: positivity transports between phases;
* `covariant_weighted_phase_common_critical`: the envelope has the critical point of each phase;
* the transport, specialized to the two phases at `β = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedPhaseCommonCritical

open _root_.StatMech _root_.StatMech.OSSS
open Lattice FK Percolation
open FKSharpnessWeightedPeriodic FKSharpnessWeightedInfiniteVolume
open FKSharpnessWeightedPhaseClose

/-- A two-phase labelling of `ℤ²`: whether the first coordinate is `0`. -/
def phase2 (x : Site 2) : Bool := decide (x 0 = 0)

/-- Both phases occur. -/
theorem phase2_surjective : Function.Surjective phase2 := by
  intro b
  cases b
  · exact ⟨fun _ => 1, by simp [phase2]⟩
  · exact ⟨0, by simp [phase2]⟩

/-- The homogeneous coupling, read through the two-phase labelling, is phase-covariant. -/
theorem phase2_covariant :
    PhaseCovariant (fun _ : Sym2 (Site 2) => (1 : ℝ)) phase2 (fun _ _ => 1) :=
  fun _ _ => rfl

-- Positivity transports between the two phases (unconditional).
example : CovariantWeightedPhasePositivityTransport 2 (fun _ => 1) phase2 (fun _ _ => 1)
    (fun _ => one_pos) phase2_surjective phase2_covariant 2 (by norm_num) :=
  covariantWeightedPhasePositivityTransport _ _ _ (fun _ => one_pos) phase2_surjective
    phase2_covariant 2 (by norm_num)

-- The envelope and the phase `true` have the same critical point (unconditional).
example : sSup {beta | Finset.univ.sup' Finset.univ_nonempty
      (fun b => weightedPhaseThetaProfile 2 (fun _ _ => 1)
        (phase2_covariant.phaseCoupling_pos phase2_surjective (fun _ => one_pos)) 2
        (by norm_num) b beta) = 0} =
    sSup {beta | weightedPhaseThetaProfile 2 (fun _ _ => 1)
      (phase2_covariant.phaseCoupling_pos phase2_surjective (fun _ => one_pos)) 2
      (by norm_num) true beta = 0} :=
  covariant_weighted_phase_common_critical _ _ _ (fun _ => one_pos) phase2_surjective
    phase2_covariant 2 (by norm_num) true

-- The transport, applied at `β = 1`: phase `true` percolates iff phase `false` does.
example : 0 < weightedPhaseThetaProfile 2 (fun _ _ => 1)
      (phase2_covariant.phaseCoupling_pos phase2_surjective (fun _ => one_pos)) 2
      (by norm_num) true 1 ↔
    0 < weightedPhaseThetaProfile 2 (fun _ _ => 1)
      (phase2_covariant.phaseCoupling_pos phase2_surjective (fun _ => one_pos)) 2
      (by norm_num) false 1 :=
  covariantWeightedPhasePositivityTransport _ _ _ (fun _ => one_pos) phase2_surjective
    phase2_covariant 2 (by norm_num) true false 1

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedPhaseCommonCritical
