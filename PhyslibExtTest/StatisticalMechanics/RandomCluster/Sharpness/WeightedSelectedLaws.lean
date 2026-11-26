/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedSelectedLaws

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedSelectedLaws`

* `weightedOpenTolerance` evaluates to `1/3` at `p = 1/2`, `q = 2`, and is positive;
* `weightedPhaseInfinite_hasBoxFiniteEnergy` for the homogeneous one-phase law on `ℤ²`;
* `weightedSelectedPhaseFiniteEnergy`: the finite-energy predicate holds for that coupling;
* `coherentTranslatedLaw_covariant`: translated laws are covariant.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedSelectedLaws

open MeasureTheory _root_.StatMech _root_.StatMech.OSSS
open Lattice FK Percolation
open FKSharpnessWeightedPeriodic FKSharpnessWeightedInfiniteVolume
open FKSharpnessWeightedPhaseTransport FKSharpnessWeightedSelectedLaws

/-- The homogeneous one-phase coupling on `ℤ^d`. -/
def unitJ (d : ℕ) : Unit → Sym2 (Site d) → ℝ := fun _ _ => 1

-- The open tolerance at `p = 1/2`, `q = 2` is `1/3`.
example : weightedOpenTolerance (1 / 2) 2 = 1 / 3 := by
  norm_num [weightedOpenTolerance]

-- The open tolerance is positive for `0 < p < 1`, `q ≥ 1`.
example : 0 < weightedOpenTolerance (1 / 2) 2 :=
  weightedOpenTolerance_pos (by norm_num) (by norm_num) (by norm_num)

-- The infinite-volume homogeneous phase law has box finite energy.
example : HasBoxFiniteEnergy (weightedPhaseInfiniteVolume 2 (unitJ 2) () (fun _ => one_pos) 2 1
    (zero_lt_one.trans_le (by norm_num)) one_pos : Measure (ConfigSpace (Sym2 (Site 2)))) :=
  weightedPhaseInfinite_hasBoxFiniteEnergy 2 (unitJ 2) () (fun _ => one_pos) 2 1 (by norm_num)
    one_pos

-- `WeightedSelectedPhaseFiniteEnergy` holds for the homogeneous coupling.
example : WeightedSelectedPhaseFiniteEnergy 2 (unitJ 2) (fun _ _ => one_pos) 2
    (zero_lt_one.trans_le (by norm_num)) :=
  weightedSelectedPhaseFiniteEnergy 2 (unitJ 2) (fun _ _ => one_pos) 2 (by norm_num)

-- Translated laws are covariant.
example (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) (x y : Site 2) :
    (coherentTranslatedLaw mu y : Measure (ConfigSpace (Sym2 (Site 2)))) =
      (coherentTranslatedLaw mu x : Measure (ConfigSpace (Sym2 (Site 2)))).map
        (ConfigSpace.shift (Multiplicative.ofAdd (x - y))) :=
  coherentTranslatedLaw_covariant mu x y

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedSelectedLaws
