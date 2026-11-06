/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnInputSparse

/-! Exact original physical input columns admit an eight-state linear reduction. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Eight original physical columns chosen for the source tensor reduction. -/
def generatedNinthInputBasisColumn : Fin 8 → Fin 24 :=
  ![1, 0, 2, 3, 5, 6, 8, 10]

/-- Integer coefficients of the source column reduction, with the stated common denominator. -/
def generatedNinthInputBasisCoefficients : Fin 24 → Fin 8 → ℤ :=
  ![![0, 1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![-1, -1, 0, 1, 1, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![2, 0, 0, -1, -1, 2, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1],
    ![-1, -1, 1, 0, 1, 0, 0, -1],
    ![1, 1, 1, -1, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 1, -1, 0, 1, 1, 0],
    ![1, 0, 1, -1, 0, 1, 1, 0],
    ![-1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 1, 1, -1, -1, 2, 1, 1],
    ![1, 0, 0, 0, -1, 1, 1, 1],
    ![-1, 1, -1, 0, 0, 0, -1, -1],
    ![-1, 0, 0, 0, 1, -1, -1, -1],
    ![1, 1, 0, -1, -1, 1, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Check the exact physical coefficient identity for all64 input roots and all24 output columns.
/-- Every original signed input root retains its exact physical row in the eight-state reduction. -/
theorem generatedNinth_input_basis_root_coordinate : ∀ k : Fin 64, ∀ i : Fin 24,
    1 * generatedNinthFrameVectorData 9 (generatedFifthOddRootOutputData k).2 i =
      ∑ b : Fin 8, generatedNinthInputBasisCoefficients i b *
        generatedNinthFrameVectorData 9 (generatedFifthOddRootOutputData k).2
          (generatedNinthInputBasisColumn b) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
