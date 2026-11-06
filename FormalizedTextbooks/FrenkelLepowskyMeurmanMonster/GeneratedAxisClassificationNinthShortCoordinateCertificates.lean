/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOriginalShortMaskPhase

/-! An integer basis-vector certificate and a binary coordinate certificate bind an intrinsic
preferred mask. The inverse identity is the actual repository Leech basis identity, so each
finite certificate can use multiplication instead of recomputing integer division. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The checked denominator-eight inverse recovers every integer basis-coordinate vector. -/
theorem generatedNinth_leech_coordinates_basis_mul (c : Fin 24 → ℤ) :
    monsterNortonLeechCoordinates (leechBasisMatrix *ᵥ c) = c := by
  funext i
  unfold monsterNortonLeechCoordinates
  rw [Matrix.mulVec_mulVec, monsterNortonLeechInverseEight_certificate]
  simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply]

/-- Genuine integer and binary certificates bind the full original source's intrinsic mask. -/
theorem generatedNinth_original_short_mask_of_coordinates
    (a : generatedNinthOriginalShortLabel) (c : Fin 24 → ℤ) (n : ℕ)
    (hint : generatedNinthOriginalShortIntegral a = leechBasisMatrix *ᵥ c)
    (hbin : leechHyperbolicInverse *ᵥ integerParity c =
      monsterCo1GeometryBinaryMaskDecode n) :
    toAdd (generatedNinthOriginalShortQ a).base = monsterCo1GeometryBinaryMaskDecode n := by
  change leechHyperbolicInverse *ᵥ integerParity
    (monsterNortonLeechCoordinates (generatedNinthOriginalShortIntegral a)) = _
  rw [hint, generatedNinth_leech_coordinates_basis_mul, hbin]

/-- Genuine integer and binary certificates bind any actual preferred target mask. -/
theorem generatedNinth_preferred_short_mask_of_coordinates
    (s : GriessShortIndex) (c : Fin 24 → ℤ) (n : ℕ)
    (hint : griessShortIntegral s = leechBasisMatrix *ᵥ c)
    (hbin : leechHyperbolicInverse *ᵥ integerParity c =
      monsterCo1GeometryBinaryMaskDecode n) :
    toAdd (monsterNortonShortQ s).base = monsterCo1GeometryBinaryMaskDecode n := by
  change leechHyperbolicInverse *ᵥ integerParity
    (monsterNortonLeechCoordinates (griessShortIntegral s)) = _
  rw [hint, generatedNinth_leech_coordinates_basis_mul, hbin]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
