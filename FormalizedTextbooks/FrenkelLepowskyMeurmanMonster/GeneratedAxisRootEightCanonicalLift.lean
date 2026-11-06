/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTransport
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialWords
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignLocal

/-! An actual local lift of the literal canonical transport retains all original source phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each original permutation letter uses its actual source spin lift. -/
def generatedFifthRootEightCanonicalFiberLetter (k : Fin 4) : localFiberSubgroup :=
  if h : k.val < 2 then monsterSourcePermutationFiber ⟨k.val, by omega⟩
  else (monsterSourcePermutationFiber ⟨k.val - 2, by omega⟩)⁻¹

/-- The full chronological source permutation lift for each monomial factor. -/
def generatedFifthRootEightCanonicalPermutationFiber (k : Fin 3) : localFiberSubgroup :=
  (generatedFifthRootEightCanonicalPermutationWords k).foldl
    (fun f j => generatedFifthRootEightCanonicalFiberLetter j * f) 1

/-- Each source lift has exactly the prescribed original spatial letter. -/
theorem generatedFifthRootEight_canonical_fiber_letter_spatial (k : Fin 4) :
    generatedFourthMonomialSpatialProjection (generatedFifthRootEightCanonicalFiberLetter k) =
      golayPermutationHom (generatedFifthRootEightCanonicalPermutationLetter k) := by
  unfold generatedFifthRootEightCanonicalFiberLetter
    generatedFifthRootEightCanonicalPermutationLetter
  split_ifs with h
  · rfl
  · rw [map_inv, map_inv]
    rfl

/-- Complete source permutation words retain their full genuine spatial projection. -/
theorem generatedFifthRootEight_canonical_permutation_fiber_spatial (k : Fin 3) :
    (generatedFifthRootEightCanonicalPermutationFiber k).val.2 =
      golayPermutationIsometry (generatedFifthRootEightCanonicalPermutation k) := by
  have aux (w : List (Fin 4)) (f : localFiberSubgroup) (p : golayAutomorphismSubgroup)
      (h : generatedFourthMonomialSpatialProjection f = golayPermutationHom p) :
      generatedFourthMonomialSpatialProjection
        (w.foldl (fun a j => generatedFifthRootEightCanonicalFiberLetter j * a) f) =
      golayPermutationHom
        (w.foldl (fun a j => generatedFifthRootEightCanonicalPermutationLetter j * a) p) := by
    induction w generalizing f p with
    | nil => exact h
    | cons j w ih =>
      apply ih
      rw [map_mul, map_mul, h, generatedFifthRootEight_canonical_fiber_letter_spatial]
  exact aux _ 1 1 (by rw [map_one, map_one])

/-- Actual source signs and source permutation phases form each local monomial factor. -/
def generatedFifthRootEightCanonicalMonomialLocal (k : Fin 3) : H :=
  generatedFifthSignLocal (generatedFifthRootEightCanonicalSignLabels k) 0 *
    localFiberIntoH (generatedFifthRootEightCanonicalPermutationFiber k)

/-- Each genuine local monomial factor projects to its actual Conway isometry. -/
theorem generatedFifthRootEight_canonical_monomial_local_projection (k : Fin 3) :
    projH (generatedFifthRootEightCanonicalMonomialLocal k) =
      QuotientGroup.mk' signsSubgroup (generatedFifthRootEightCanonicalMonomial k) := by
  have hs : sourceGeneratedSignCode (generatedFifthRootEightCanonicalSignLabels k) =
      golayCodeLabelEquiv (generatedFifthRootEightCanonicalSignLabels k) := by
    apply Subtype.ext
    exact (golayCodeLabelEquiv_val _).symm
  rw [generatedFifthRootEightCanonicalMonomialLocal, map_mul,
    generatedFifth_sign_local_projection, hs, generatedFifthRootEightCanonicalMonomial, map_mul]
  congr 1
  change QuotientGroup.mk' signsSubgroup
    (generatedFifthRootEightCanonicalPermutationFiber k).val.2 = _
  rw [generatedFifthRootEight_canonical_permutation_fiber_spatial]

/-- The exact original canonical transport in the full local group. -/
def generatedFifthRootEightCanonicalLocal : H :=
  generatedFifthRootEightCanonicalMonomialLocal 2 * localFiberIntoH xiSpinLocalFiber *
    localFiberIntoH xiSpinLocalFiber * generatedFifthRootEightCanonicalMonomialLocal 1 *
    localFiberIntoH xiSpinLocalFiber * generatedFifthRootEightCanonicalMonomialLocal 0

/-- No original source phase is discarded in the complete local transport projection. -/
theorem generatedFifthRootEight_canonical_local_projection :
    projH generatedFifthRootEightCanonicalLocal =
      QuotientGroup.mk' signsSubgroup generatedFifthRootEightCanonicalTransport := by
  simp only [generatedFifthRootEightCanonicalLocal, generatedFifthRootEightCanonicalTransport,
    map_mul, generatedFifthRootEight_canonical_monomial_local_projection]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
