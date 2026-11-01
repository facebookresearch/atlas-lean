/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitPermutations
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightFlagData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100Flag
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2XiTransitions

/-! A literal original Conway transport from the root-eight flag to the canonical norm-six flag.
Only its actual lattice action is asserted here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

/-- Original forward or inverse Golay permutation generators. -/
def generatedFifthRootEightCanonicalPermutationLetter (k : Fin 4) :
    golayAutomorphismSubgroup :=
  if h : k.val < 2 then omegaOrbitGolayPermutation ⟨k.val, by omega⟩
  else (omegaOrbitGolayPermutation ⟨k.val - 2, by omega⟩)⁻¹

/-- Literal original permutation words in chronological order. -/
def generatedFifthRootEightCanonicalPermutationWords : Fin 3 → List (Fin 4) :=
![[2, 2, 1, 0, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 0, 0, 0, 1, 2, 2, 1, 0, 0, 1, 2, 2, 2,
    1, 0, 0],
  [2, 2, 3, 0, 0, 0, 3, 2, 2, 3, 0, 0, 3, 2, 2, 2, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 2, 1, 0, 0,
    1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 2, 3, 0, 0, 3, 0, 3, 2,
    3, 2, 1, 0, 1, 0, 1, 2, 1, 2, 2, 2, 1, 0, 0, 1, 0, 0, 0],
  [2, 2, 2, 3, 2, 2, 3, 0, 0, 0, 3, 0, 3, 2, 3, 2, 3]]

/-- Each transport permutation is a product of actual original Golay automorphisms. -/
def generatedFifthRootEightCanonicalPermutation (k : Fin 3) : golayAutomorphismSubgroup :=
  (generatedFifthRootEightCanonicalPermutationWords k).foldl
    (fun p j => generatedFifthRootEightCanonicalPermutationLetter j * p) 1

/-- The three original Golay sign labels after combining consecutive monomial stages. -/
def generatedFifthRootEightCanonicalSignLabels : Fin 3 → Fin 4096 := ![1536, 3220, 165]

/-- The three genuine monomial factors of the transport. -/
def generatedFifthRootEightCanonicalMonomial (k : Fin 3) : leechIsomSubgroup :=
  golaySignIsometry (golayCodeLabelEquiv (generatedFifthRootEightCanonicalSignLabels k)) *
    golayPermutationIsometry (generatedFifthRootEightCanonicalPermutation k)

/-- Original integer coordinates at all six consecutive action stages. -/
def generatedFifthRootEightCanonicalRootStages : Fin 7 → Fin 24 → ℤ :=
![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 0],
  ![0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Original joining-vector coordinates at the same six stages. -/
def generatedFifthRootEightCanonicalCompanionStages : Fin 7 → Fin 24 → ℤ :=
![![0, 2, 2, 0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0, 0, 4, -2, -2, 2, 0, 2, 0],
  ![2, 0, -4, 0, 2, 2, -2, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0],
  ![-3, 1, -3, 1, -1, 1, -3, -1, 1, -1, 1, -1, -1, -1, 1, 1, -1, 1, 1, -1, -1, -1, -1, -1],
  ![3, 1, -3, -3, -1, -1, -1, 1, -1, -1, -1, 1, 1, -1, -1, -1, -1, -1, 1, -1, -1, 1, -1, -1],
  ![-4, 2, -2, -2, 0, 0, 0, 2, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0],
  ![1, 5, 1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1, -1, 1, -1, 1, 1, -1, -1],
  ![5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

/-- Both flag vectors use the same six complete spatial stages. -/
def generatedFifthRootEightCanonicalStages (b : Bool) : Fin 7 → Fin 24 → ℤ :=
  if b then generatedFifthRootEightCanonicalRootStages
  else generatedFifthRootEightCanonicalCompanionStages

/-- Literal integer form of a complete genuine monomial stage. -/
def generatedFifthRootEightCanonicalMonomialInteger (k : Fin 3) (v : Fin 24 → ℤ) :
    Fin 24 → ℤ :=
  golayIntegerSign (golayCodeLabelEquiv
    (generatedFifthRootEightCanonicalSignLabels k)).val
    (golayIntegerPermute (generatedFifthRootEightCanonicalPermutation k).val v)

set_option maxHeartbeats 64000000 in
-- Check every coordinate of both vectors, including all original permutation words.
/-- All three monomial stages carry both original vectors to their stated integer coordinates. -/
theorem generatedFifthRootEight_canonical_monomial_certificates : ∀ b : Bool,
    generatedFifthRootEightCanonicalMonomialInteger 0
      (generatedFifthRootEightCanonicalStages b 0) =
        generatedFifthRootEightCanonicalStages b 1 ∧
    generatedFifthRootEightCanonicalMonomialInteger 1
      (generatedFifthRootEightCanonicalStages b 2) =
        generatedFifthRootEightCanonicalStages b 3 ∧
    generatedFifthRootEightCanonicalMonomialInteger 2
      (generatedFifthRootEightCanonicalStages b 5) =
        generatedFifthRootEightCanonicalStages b 6 := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check all physical coordinates against the original Xi matrix.
/-- All three Xi stages have the full original integer numerator action. -/
theorem generatedFifthRootEight_canonical_xi_certificates : ∀ b : Bool,
    co1XiNumerator *ᵥ generatedFifthRootEightCanonicalStages b 1 =
      (2 : ℕ) • generatedFifthRootEightCanonicalStages b 2 ∧
    co1XiNumerator *ᵥ generatedFifthRootEightCanonicalStages b 3 =
      (2 : ℕ) • generatedFifthRootEightCanonicalStages b 4 ∧
    co1XiNumerator *ᵥ generatedFifthRootEightCanonicalStages b 4 =
      (2 : ℕ) • generatedFifthRootEightCanonicalStages b 5 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
