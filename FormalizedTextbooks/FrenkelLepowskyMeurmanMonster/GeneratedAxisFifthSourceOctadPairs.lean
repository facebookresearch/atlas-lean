/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPermutationGeneration

/-! Actual five-generator transversals on the 28 unordered pairs of source octad14. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

/-- Four proved pair-fixing generators and the original source P0 permutation. -/
def generatedFifthSourceOctadPermutation : Fin 5 → golayAutomorphismSubgroup :=
  ![generatedFourthMonomialPermutation 0, generatedFourthMonomialPermutation 1,
    generatedFourthMonomialPermutation 2, generatedFourthMonomialPermutation 3,
    omegaOrbitGolayPermutation 0]

/-- All genuine unordered pairs inside the physical support of source octad14. -/
def generatedFifthSourceOctadPair : Fin 28 → Finset (Fin 24) :=
  ![{4, 5},
    {4, 6},
    {4, 7},
    {4, 8},
    {4, 9},
    {4, 10},
    {4, 11},
    {5, 6},
    {5, 7},
    {5, 8},
    {5, 9},
    {5, 10},
    {5, 11},
    {6, 7},
    {6, 8},
    {6, 9},
    {6, 10},
    {6, 11},
    {7, 8},
    {7, 9},
    {7, 10},
    {7, 11},
    {8, 9},
    {8, 10},
    {8, 11},
    {9, 10},
    {9, 11},
    {10, 11}]

/-- Actual positive generator words carrying the original unordered pair to every target. -/
def generatedFifthSourceOctadPairWord : Fin 28 → List (Fin 5) :=
  ![[0, 2, 3, 4],
    [2, 0, 2, 4],
    [0, 2, 4],
    [4, 4, 4],
    [4, 1, 2, 4],
    [4, 4, 0, 2, 4],
    [1, 4, 4, 4],
    [2, 3, 4],
    [0, 1, 2, 4],
    [4, 3, 4],
    [4, 4],
    [1, 2, 4],
    [4, 0, 2, 4],
    [1, 0, 1, 2, 4],
    [4, 3, 2, 4],
    [3, 2, 4],
    [2, 4],
    [1, 4, 3, 4],
    [2, 4, 3, 2, 4],
    [3, 4],
    [4],
    [4, 4, 4, 4],
    [4, 0, 3, 4],
    [3, 2, 4, 0, 2, 4],
    [],
    [0, 3, 4],
    [2, 4, 0, 2, 4],
    [3, 4, 0, 3, 4]]

/-- The original permutation represented by each displayed actual word. -/
def generatedFifthSourceOctadPairRep (r : Fin 28) : golayAutomorphismSubgroup :=
  ((generatedFifthSourceOctadPairWord r).map generatedFifthSourceOctadPermutation).prod

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Verify all 28 actual source-word images of the two physical coordinates.
/-- Every displayed pair representative has the asserted genuine target. -/
theorem generatedFifthSourceOctadPair_certificate : ∀ r : Fin 28,
    ({(generatedFifthSourceOctadPairRep r).val 8,
      (generatedFifthSourceOctadPairRep r).val 11} : Finset (Fin 24)) =
        generatedFifthSourceOctadPair r := by
  decide +kernel

/-- The 28 pair labels are distinct actual physical pairs. -/
theorem generatedFifthSourceOctadPair_injective :
    Function.Injective generatedFifthSourceOctadPair := by
  decide +kernel

/-- Any two distinct coordinates of the source octad form one of the 28 actual pairs. -/
theorem generatedFifthSourceOctadPair_covers : ∀ a b : Fin 24,
    4 ≤ a.val → a.val < 12 → 4 ≤ b.val → b.val < 12 → a ≠ b →
      ∃ r : Fin 28, ({a, b} : Finset (Fin 24)) = generatedFifthSourceOctadPair r := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
