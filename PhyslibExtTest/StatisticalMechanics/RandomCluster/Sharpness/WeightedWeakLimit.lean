/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedWeakLimit

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedWeakLimit`

For the homogeneous one-phase coupling on `ℤ²`, `q = 2`, `β = 1`:
* `weightedPhaseFiniteMeasure_tendsto_selected`: the finite measures converge weakly to the
  selected law (the whole sequence, not a subsequence);
* `weightedPhaseFiniteMeasure_weakLimit_unique`: every weak limit is the selected law.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedWeakLimit

open MeasureTheory _root_.StatMech _root_.StatMech.OSSS
open Lattice FK Percolation
open FKSharpnessWeightedPeriodic FKSharpnessWeightedInfiniteVolume FKSharpnessWeightedWeakLimit

/-- The homogeneous one-phase coupling on `ℤ^d`. -/
def unitJ (d : ℕ) : Unit → Sym2 (Site d) → ℝ := fun _ _ => 1

-- The finite homogeneous phase measures converge weakly to the selected law.
example : WeakConvergesTo
    (fun n => weightedPhaseFiniteMeasure 2 n (unitJ 2) () (fun _ => one_pos) 2 1
      (zero_lt_one.trans_le (by norm_num)) one_pos)
    (weightedPhaseInfiniteVolume 2 (unitJ 2) () (fun _ => one_pos) 2 1
      (zero_lt_one.trans_le (by norm_num)) one_pos) :=
  weightedPhaseFiniteMeasure_tendsto_selected 2 (unitJ 2) () (fun _ => one_pos) 2 1 (by norm_num)
    one_pos

-- Any weak limit of the finite measures is the selected law.
example (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2))))
    (hmu : WeakConvergesTo
      (fun n => weightedPhaseFiniteMeasure 2 n (unitJ 2) () (fun _ => one_pos) 2 1
        (zero_lt_one.trans_le (by norm_num)) one_pos) mu) :
    mu = weightedPhaseInfiniteVolume 2 (unitJ 2) () (fun _ => one_pos) 2 1
      (zero_lt_one.trans_le (by norm_num)) one_pos :=
  weightedPhaseFiniteMeasure_weakLimit_unique 2 (unitJ 2) () (fun _ => one_pos) 2 1 (by norm_num)
    one_pos mu hmu

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedWeakLimit
