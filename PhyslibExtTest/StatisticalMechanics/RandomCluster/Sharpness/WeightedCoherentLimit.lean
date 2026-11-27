/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedCoherentLimit

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedCoherentLimit`

For the homogeneous one-phase coupling (`P = Unit`, all couplings `1`) on `ℤ²`, `q = 2`:
* `weightedPhaseWiredTheta_tendsto_infiniteTheta`: finite-volume crossing probabilities converge
  at `β = 1`;
* `weightedPhaseDiagonalTailConvergence_of_one_le`: the diagonal tail-convergence predicate
  holds, so it is non-vacuous;
* the predicate, unfolded at `β = 1`, recovers the convergence statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedCoherentLimit

open Filter _root_.StatMech _root_.StatMech.OSSS
open FKSharpnessWeightedCoherentLimit FKSharpnessWeightedInfiniteVolume FKSharpnessWeightedPeriodic

/-- The homogeneous one-phase coupling on `ℤ^d`. -/
def unitJ (d : ℕ) : Unit → Sym2 (Lattice.Site d) → ℝ := fun _ _ => 1

/-- The homogeneous coupling is positive. -/
theorem unitJ_pos (d : ℕ) : ∀ a e, 0 < unitJ d a e := fun _ _ => one_pos

-- Convergence of the finite-volume crossing probabilities at `β = 1`, `q = 2`.
example : Tendsto (weightedPhaseWiredTheta 2 (unitJ 2) () 2 1) atTop
    (nhds (weightedPhaseInfiniteTheta 2 (unitJ 2) () (unitJ_pos 2 ()) 2 1
      (by norm_num) one_pos)) :=
  weightedPhaseWiredTheta_tendsto_infiniteTheta 2 (unitJ 2) () (unitJ_pos 2 ()) 2 1
    (by norm_num) one_pos

-- The diagonal tail-convergence predicate holds for the homogeneous coupling.
example : WeightedPhaseDiagonalTailConvergence 2 (unitJ 2) (unitJ_pos 2) 2 :=
  weightedPhaseDiagonalTailConvergence_of_one_le 2 (unitJ 2) (unitJ_pos 2) 2 (by norm_num)

-- Specializing the predicate recovers convergence at `β = 1` in `d = 3`.
example : Tendsto (weightedPhaseWiredTheta 3 (unitJ 3) () 2 1) atTop
    (nhds (weightedPhaseInfiniteTheta 3 (unitJ 3) () (unitJ_pos 3 ()) 2 1
      (by norm_num) one_pos)) :=
  weightedPhaseDiagonalTailConvergence_of_one_le 3 (unitJ 3) (unitJ_pos 3) 2 (by norm_num)
    () 1 one_pos (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedCoherentLimit
