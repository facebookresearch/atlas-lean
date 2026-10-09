/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.Grover.IterationBounds

@[expose] public section

/-!
# Tests for the standard Grover iteration choice

The four-state, one-target search exercises the phase-distance bound, the
failure bound, the square-root iteration bound, and the one-quarter exact
success corollary through the public API.
-/

namespace Cslib.Grover.IterationBoundsTests

def oneMarked : Finset (Fin 4) := {0}

theorem oneMarked_nonempty : oneMarked.Nonempty := by
  simp [oneMarked]

theorem oneMarked_compl_nonempty : oneMarkedᶜ.Nonempty := by
  refine ⟨1, ?_⟩
  simp [oneMarked]

example :
    |groverPhase oneMarked (floorIterations oneMarked) - Real.pi / 2| ≤
      groverAngle oneMarked :=
  floorIterations_phase_distance oneMarked oneMarked_nonempty

example :
    1 - markedProbability oneMarked
        (groverIterate oneMarked (floorIterations oneMarked)
          (uniformAmplitude (Fin 4))) ≤ 1 / 4 := by
  simpa [oneMarked] using
    floorIterations_failure_probability_le oneMarked oneMarked_nonempty
      oneMarked_compl_nonempty

example :
    (floorIterations oneMarked : ℝ) ≤
      Real.pi / 4 * Real.sqrt 4 := by
  simpa [oneMarked] using
    floorIterations_le_sqrt_ratio oneMarked oneMarked_nonempty

example :
    markedProbability oneMarked
        (groverIterate oneMarked 1 (uniformAmplitude (Fin 4))) = 1 := by
  apply one_step_success_of_four_mul_card_eq oneMarked oneMarked_nonempty
  norm_num [oneMarked]

end Cslib.Grover.IterationBoundsTests
