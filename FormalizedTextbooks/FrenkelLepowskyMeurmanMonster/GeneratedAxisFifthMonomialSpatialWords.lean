/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMatrixRecognition

/-! Six actual monomial permutation words for the selected fifth frame system.
Full-axis fixation and generation are separate proof obligations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An actual coordinate transport from source octad14 to selected octad2052. -/
def generatedFifthMonomialTransportWord : List (Fin 2 × Bool) := [(0, false), (1, false), (0,
      false), (1, false), (0, false), (0, false), (0, false), (1, false), (0, false), (0, false),
      (1, false)]

set_option maxRecDepth 10000 in
/-- Six literal source permutation words obtained from the actual system orbit. -/
def generatedFifthMonomialSourceWord : Fin 6 → List (Fin 2 × Bool) :=
  ![[(0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false), (0, true),
      (0, true), (0, true), (1, false), (0, false), (0, false)],
    [(0, true), (1, true), (0, true), (0, true), (1, true), (0, false), (1, false), (0, true),
      (1, false), (0, false), (0, false), (1, false), (0, false)],
    [(0, true), (1, true), (0, false), (0, false), (0, false), (1, true), (0, true), (0, true),
      (0, true), (1, false), (0, false), (1, true), (0, true), (0, true), (1, true), (0, true),
      (0, true), (1, false), (0, false), (0, false), (1, false), (0, false), (0, false), (1,
      false), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false), (0, true),
      (0, true), (0, true), (1, false), (0, false)],
    [(1, true), (0, true), (0, true), (1, true), (0, true), (0, true), (1, true), (0, false), (0,
      false), (1, false), (0, false), (0, false), (1, false), (0, true), (0, true), (1, true),
      (0, false), (0, false), (0, false), (1, false), (0, true), (0, true), (0, true), (1,
      false), (0, false), (0, false), (1, true), (0, true), (0, true), (1, true), (0, true), (0,
      true), (1, false), (0, false), (0, false), (1, false), (0, false), (0, false), (1,
      false)],
    [(1, true), (0, true), (0, true), (1, true), (0, true), (0, true), (1, true), (0, false), (0,
      false), (1, false), (0, false), (0, false), (1, false), (0, true), (0, true), (1, true),
      (0, true), (0, true), (1, true), (0, false), (1, false), (0, true), (1, false), (0, false),
      (0, false), (1, false), (0, false), (0, false)],
    [(1, true), (0, true), (0, true), (1, true), (0, true), (0, true), (1, true), (0, false), (0,
      false), (1, false), (0, false), (0, false), (1, false), (0, true), (1, true), (0, true),
      (0, true), (1, true), (0, false), (1, true), (0, true), (1, false), (0, false), (0, false),
      (1, false), (0, false), (0, false), (0, false)]]

/-- The original phase-correct local source transport. -/
def generatedFifthMonomialTransportFiber : localFiberSubgroup :=
  (generatedFifthMonomialTransportWord.map generatedFourthMonomialFiberLetter).prod

/-- Its genuine Golay coordinate permutation. -/
def generatedFifthMonomialTransportPermutation : golayAutomorphismSubgroup :=
  (generatedFifthMonomialTransportWord.map generatedFourthMonomialPermutationLetter).prod

/-- The actual phase-correct local word for each selected-coordinate monomial permutation. -/
def generatedFifthMonomialSpatialFiber (k : Fin 6) : localFiberSubgroup :=
  generatedFifthMonomialTransportFiber *
    ((generatedFifthMonomialSourceWord k).map generatedFourthMonomialFiberLetter).prod *
      generatedFifthMonomialTransportFiber⁻¹

/-- The genuine physical permutation of the same original local word. -/
def generatedFifthMonomialSpatialPermutation (k : Fin 6) : golayAutomorphismSubgroup :=
  generatedFifthMonomialTransportPermutation *
    ((generatedFifthMonomialSourceWord k).map generatedFourthMonomialPermutationLetter).prod *
      generatedFifthMonomialTransportPermutation⁻¹

/-- Literal physical coordinate arrays for the six genuine selected permutation words. -/
def generatedFifthMonomialSpatialForward : Fin 6 → Fin 24 → Fin 24 :=
  ![![0, 2, 1, 3, 4, 7, 6, 5, 21, 20, 22, 23, 13, 12, 14, 15, 17, 16, 18, 19, 9, 8, 10, 11],
    ![2, 3, 0, 1, 7, 6, 5, 4, 8, 9, 10, 11, 13, 12, 15, 14, 16, 17, 18, 19, 21, 20, 23, 22],
    ![3, 1, 2, 0, 4, 7, 6, 5, 22, 23, 21, 20, 12, 13, 15, 14, 17, 16, 18, 19, 11, 10, 8, 9],
    ![0, 2, 1, 3, 14, 12, 15, 13, 11, 9, 10, 8, 5, 7, 4, 6, 17, 16, 18, 19, 20, 23, 22, 21],
    ![3, 1, 16, 18, 5, 20, 7, 22, 23, 4, 6, 21, 10, 9, 13, 12, 17, 2, 0, 19, 14, 11, 15, 8],
    ![19, 17, 0, 2, 6, 23, 4, 21, 20, 7, 5, 22, 13, 12, 10, 9, 1, 18, 16, 3, 8, 15, 11, 14]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Bind the six word products to all 144 actual physical coordinate images.
/-- Every literal physical array is the actual original source-word permutation. -/
theorem generatedFifthMonomialSpatial_forward : ∀ k : Fin 6, ∀ i : Fin 24,
    (generatedFifthMonomialSpatialPermutation k).val i =
      generatedFifthMonomialSpatialForward k i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
