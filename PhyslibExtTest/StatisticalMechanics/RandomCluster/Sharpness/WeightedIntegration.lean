/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedIntegration

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedIntegration`

For the homogeneous coupling `J = 1` with one phase (`P = Unit`) on `ℤ²`, `q = 2`, `β = 1`:
* `weightedPhaseSum_differential_integration` gives the integrated phase-sum inequality at
  radius `1` with `Jmin = Jmax = 1`;
* `weightedPhasePhysical_le_localized_half`: the physical crossing at radius `2` is at most the
  localized crossing at radius `1`;
* `weightedPhaseSum` with one phase is the single profile.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedIntegration

open MeasureTheory _root_.StatMech _root_.StatMech.OSSS
open FKSharpnessWeightedIntegration FKSharpnessWeightedPeriodic FKSharpnessWeightedInfiniteVolume
open FKSharpnessWeightedStrict Lattice FK RevealmentConstruction WiredBoxDifferential
open WiredBoxLocalized WiredBoxOffCentre

/-- The homogeneous one-phase coupling on `ℤ^d`. -/
def unitJ (d : ℕ) : Unit → Sym2 (Lattice.Site d) → ℝ := fun _ _ => 1

/-- The homogeneous coupling with one phase is phase-covariant. -/
theorem unit_phaseCovariant (d : ℕ) :
    PhaseCovariant (fun _ : Sym2 (Lattice.Site d) => (1 : ℝ)) (fun _ => ()) (unitJ d) :=
  fun _ _ => rfl

-- The integrated phase-sum inequality on the homogeneous one-phase model.
example : (1 * Real.exp (-(1 * 1)) ^ (2 * 2) / 8) *
      (((1 : ℕ) / weightedPhaseSumSig 2 1 (unitJ 2) 2 1 : ℝ) *
        weightedPhaseSum 2 (unitJ 2) 2 1 1) ≤
    deriv (fun b => weightedPhaseSum 2 (unitJ 2) 2 b 1) 1 :=
  weightedPhaseSum_differential_integration 2 1 le_rfl (fun _ => 1) 1 1 one_pos
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => ()) (unitJ 2) (fun _ => ⟨0, rfl⟩)
    (unit_phaseCovariant 2) 2 1 1 (by norm_num) one_pos le_rfl

-- The physical crossing at radius `2` is bounded by the localized crossing at radius `1`.
example : ((weightedPhaseFiniteMeasure 2 2 (unitJ 2) () (fun _ => one_pos) 2 1
      (zero_lt_one.trans_le (by norm_num)) one_pos : ProbabilityMeasure _) :
        Measure (ConfigSpace (Sym2 (Lattice.Site 2)))).real
      (boxBdryConnEvent 2 2) ≤
    weightedPhaseProfile 2 (unitJ 2) () 2 1 (2 / 2) :=
  weightedPhasePhysical_le_localized_half 2 2 le_rfl (unitJ 2) (fun _ _ => one_pos) () 2 1
    (by norm_num) one_pos

-- With one phase, the phase sum is the single profile.
example (n : ℕ) :
    weightedPhaseSum 2 (unitJ 2) 2 1 n = weightedPhaseProfile 2 (unitJ 2) () 2 1 n := by
  simp [weightedPhaseSum]

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedIntegration
