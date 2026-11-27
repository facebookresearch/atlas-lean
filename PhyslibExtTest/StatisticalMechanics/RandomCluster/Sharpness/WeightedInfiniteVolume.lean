/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedInfiniteVolume

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedInfiniteVolume`

For the homogeneous coupling `J = 1` with one phase (`P = Unit`) on `ℤ²`, `q = 2`, `β = 1`:
* `weightedPhaseInfiniteVolume_isLimit`: the infinite-volume measure is a subsequential weak
  limit of the finite ones;
* `weightedPhaseInfiniteTheta_nonneg`: the percolation probability is nonnegative;
* `CovariantWeightedPhasePositivityTransport` holds for one phase (non-vacuity);
* `covariant_weighted_phase_common_critical` applies with that transport hypothesis.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedInfiniteVolume

open _root_.StatMech _root_.StatMech.OSSS
open FKSharpnessWeightedInfiniteVolume FKSharpnessWeightedPeriodic

/-- The homogeneous one-phase coupling on `ℤ^d`. -/
def unitJ (d : ℕ) : Unit → Sym2 (Lattice.Site d) → ℝ := fun _ _ => 1

/-- The homogeneous coupling with one phase is phase-covariant. -/
theorem unit_phaseCovariant (d : ℕ) :
    PhaseCovariant (fun _ : Sym2 (Lattice.Site d) => (1 : ℝ)) (fun _ => ()) (unitJ d) :=
  fun _ _ => rfl

-- The infinite-volume measure is a subsequential weak limit of the finite measures.
example : ∃ phi : ℕ → ℕ, StrictMono phi ∧
    WeakConvergesTo (fun n => weightedPhaseFiniteMeasure 2 (phi n) (unitJ 2) ()
      (fun _ => one_pos) 2 1 (by norm_num) one_pos)
      (weightedPhaseInfiniteVolume 2 (unitJ 2) () (fun _ => one_pos) 2 1 (by norm_num) one_pos) :=
  weightedPhaseInfiniteVolume_isLimit 2 (unitJ 2) () (fun _ => one_pos) 2 1 (by norm_num) one_pos

-- The infinite-volume percolation probability is nonnegative.
example : 0 ≤ weightedPhaseInfiniteTheta 2 (unitJ 2) () (fun _ => one_pos) 2 1
    (by norm_num) one_pos :=
  weightedPhaseInfiniteTheta_nonneg 2 (unitJ 2) () (fun _ => one_pos) 2 1 (by norm_num) one_pos

/-- Positivity transport holds trivially with a single phase. -/
theorem unit_transport :
    CovariantWeightedPhasePositivityTransport 2 (fun _ => 1) (fun _ => ()) (unitJ 2)
      (fun _ => one_pos) (fun _ => ⟨0, rfl⟩) (unit_phaseCovariant 2) 2 (by norm_num) :=
  fun _ _ _ => Iff.rfl

-- With one phase, the envelope and the phase have the same critical point.
example : sSup {beta | Finset.univ.sup' Finset.univ_nonempty
      (fun b => weightedPhaseThetaProfile 2 (unitJ 2)
        ((unit_phaseCovariant 2).phaseCoupling_pos (fun _ => ⟨0, rfl⟩) (fun _ => one_pos))
        2 (by norm_num) b beta) = 0} =
    sSup {beta | weightedPhaseThetaProfile 2 (unitJ 2)
      ((unit_phaseCovariant 2).phaseCoupling_pos (fun _ => ⟨0, rfl⟩) (fun _ => one_pos))
      2 (by norm_num) () beta = 0} :=
  covariant_weighted_phase_common_critical 2 (fun _ => 1) (fun _ => ()) (unitJ 2)
    (fun _ => one_pos) (fun _ => ⟨0, rfl⟩) (unit_phaseCovariant 2) 2 (by norm_num)
    unit_transport ()

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedInfiniteVolume
