/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedPhaseTransport

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedPhaseTransport`

* `HasBoxFiniteEnergy` holds for the point mass at the all-open configuration (non-vacuity);
* `clusterInfiniteEvent_measure_pos_iff` applied to that measure on `ℤ²`;
* `covariantWeightedSelectedPhaseLaws_iff`: the selected-laws hypothesis splits into translation
  covariance and finite energy;
* `covariant_weighted_phase_common_critical_of_selectedLaws` applied to the homogeneous one-phase
  model under its selected-laws hypothesis.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedPhaseTransport

open MeasureTheory _root_.StatMech _root_.StatMech.OSSS
open Lattice FK Percolation
open FKSharpnessWeightedPeriodic FKSharpnessWeightedInfiniteVolume
open FKSharpnessWeightedPhaseTransport

/-- The all-open configuration on `ℤ^d`. -/
def allOpen (d : ℕ) : ConfigSpace (Sym2 (Site d)) := fun _ => true

/-- Forcing any finite edge set open fixes the all-open configuration. -/
theorem forceOpenFinset_allOpen {d : ℕ} (F : Finset (Sym2 (Site d))) :
    forceOpenFinset F (allOpen d) = allOpen d := by
  funext e
  unfold forceOpenFinset allOpen
  split_ifs <;> rfl

/-- The point mass at the all-open configuration has box finite energy (non-vacuity). -/
theorem dirac_allOpen_hasBoxFiniteEnergy (d : ℕ) :
    HasBoxFiniteEnergy (Measure.dirac (allOpen d)) := by
  intro n
  rw [Measure.map_dirac' (measurable_forceOpenFinset _), forceOpenFinset_allOpen]

-- Under the all-open point mass, infinite clusters at `0` and at `x` are equally likely positive.
example (x : Site 2) :
    0 < Measure.dirac (allOpen 2) (clusterInfiniteEvent 2 0) ↔
      0 < Measure.dirac (allOpen 2) (clusterInfiniteEvent 2 x) :=
  clusterInfiniteEvent_measure_pos_iff _ (dirac_allOpen_hasBoxFiniteEnergy 2) 0 x

-- The selected-laws hypothesis splits into translation covariance and finite energy.
example {P : Type*} (phaseJ : P → Sym2 (Site 2) → ℝ) (hJ : ∀ a e, 0 < phaseJ a e)
    (phase : Site 2 → P) :
    CovariantWeightedSelectedPhaseLaws 2 phaseJ hJ phase 2 two_pos ↔
      CovariantWeightedSelectedPhaseTranslation 2 phaseJ hJ phase 2 two_pos ∧
        WeightedSelectedPhaseFiniteEnergy 2 phaseJ hJ 2 two_pos :=
  covariantWeightedSelectedPhaseLaws_iff phaseJ hJ phase 2 two_pos

-- The common critical point, given the selected-laws hypothesis (homogeneous one-phase model).
example (hlaws : CovariantWeightedSelectedPhaseLaws 2 (fun (_ : Unit) _ => 1)
      ((show PhaseCovariant (fun _ : Sym2 (Site 2) => (1 : ℝ)) (fun _ => ()) (fun _ _ => 1)
        from fun _ _ => rfl).phaseCoupling_pos (fun _ => ⟨0, rfl⟩) (fun _ => one_pos))
      (fun _ => ()) 2 two_pos) :
    sSup {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun b => weightedPhaseThetaProfile 2 (fun (_ : Unit) _ => 1)
          ((show PhaseCovariant (fun _ : Sym2 (Site 2) => (1 : ℝ)) (fun _ => ()) (fun _ _ => 1)
            from fun _ _ => rfl).phaseCoupling_pos (fun _ => ⟨0, rfl⟩) (fun _ => one_pos))
          2 two_pos b beta) = 0} =
      sSup {beta | weightedPhaseThetaProfile 2 (fun (_ : Unit) _ => 1)
        ((show PhaseCovariant (fun _ : Sym2 (Site 2) => (1 : ℝ)) (fun _ => ()) (fun _ _ => 1)
          from fun _ _ => rfl).phaseCoupling_pos (fun _ => ⟨0, rfl⟩) (fun _ => one_pos))
        2 two_pos () beta = 0} :=
  covariant_weighted_phase_common_critical_of_selectedLaws _ _ _ (fun _ => one_pos)
    (fun _ => ⟨0, rfl⟩) (fun _ _ => rfl) 2 two_pos hlaws ()

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedPhaseTransport
