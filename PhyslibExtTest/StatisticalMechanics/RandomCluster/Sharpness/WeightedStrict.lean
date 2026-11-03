/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedStrict

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedStrict`

For the homogeneous coupling `J = 1` with one phase on `ℤ²`, `q = 2`, `β = 1`:
* `weightedStrictDenom_le_phaseEnvelopeSig` at box radius `3`;
* `weightedStrictDenom_pos`: the strict denominator is positive;
* `weightedPhaseProfile_zero`, `weightedOuterInnerConn_zero`: boundary values `1` at radius `0`;
* `weightedPhaseProfile_tendsto_infiniteTheta`: the profiles converge to `θ`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedStrict

open _root_.StatMech _root_.StatMech.OSSS
open Lattice FK RevealmentConstruction RevealmentTranslation
open WiredBoxDifferential WiredBoxLocalized WiredBoxOffCentre AdaptiveCovLowerGeom
open FKSharpnessWeighted FKSharpnessWeightedPeriodic FKSharpnessWeightedPeriodicRepair
open FKSharpnessWeightedInfiniteVolume FKSharpnessWeightedStrict

/-- The homogeneous one-phase coupling on `ℤ^d`. -/
def unitJ (d : ℕ) : Unit → Sym2 (Site d) → ℝ := fun _ _ => 1

/-- The homogeneous coupling with one phase is phase-covariant. -/
theorem unit_phaseCovariant (d : ℕ) :
    PhaseCovariant (fun _ : Sym2 (Site d) => (1 : ℝ)) (fun _ => ()) (unitJ d) :=
  fun _ _ => rfl

-- The strict denominator is bounded by the envelope sum (box radius `3`).
example : weightedStrictDenom 2 3 (fun _ => 1) 2 1 ≤
    8 * weightedPhaseEnvelopeSig 2 3 (unitJ 2) 2 1 / ((3 : ℕ) : ℝ) :=
  weightedStrictDenom_le_phaseEnvelopeSig 2 3 _ (fun _ => one_pos) (fun _ => ()) (unitJ 2)
    (fun _ => ⟨0, rfl⟩) (unit_phaseCovariant 2) 2 1 (by norm_num) one_pos

-- The strict denominator is positive.
example : 0 < weightedStrictDenom 2 3 (fun _ => 1) 2 1 :=
  weightedStrictDenom_pos 2 3 (by norm_num) _ (fun _ => one_pos) 2 1 (by norm_num) one_pos

-- The profile is `1` at radius `0`, and the outer-inner connection at radius `0` is `1`.
example : weightedPhaseProfile 2 (unitJ 2) () 2 1 0 = 1 ∧
    weightedOuterInnerConn 2 3 (fun _ => 1) 2 1 0 0 = 1 :=
  ⟨weightedPhaseProfile_zero _ _ _ _ _,
    weightedOuterInnerConn_zero 2 3 _ (fun _ => one_pos) 2 1 (by norm_num) one_pos 0⟩

-- The profiles converge to the infinite-volume percolation probability.
example : Filter.Tendsto (weightedPhaseProfile 2 (unitJ 2) () 2 1) Filter.atTop
    (nhds (weightedPhaseInfiniteTheta 2 (unitJ 2) () (fun _ => one_pos) 2 1
      (zero_lt_one.trans_le (by norm_num)) one_pos)) :=
  weightedPhaseProfile_tendsto_infiniteTheta 2 (unitJ 2) () (fun _ => one_pos) 2 1 (by norm_num)
    one_pos

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedStrict
