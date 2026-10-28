/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPreferredMaskFastData

/-! Complete original preferred masks from exact bounded catalogue lookups. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- All negative physical positions in the original preferred octad sign pattern. -/
def generatedAxisGlobalPreferredMaskOctadNegative (j : Fin 759) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun (k : Fin 8) (m : ℕ) =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedAxisGlobalPreferredMaskOctadCoordinate j k).val else 0) ||| m) 0

/-- The complete original preferred mask, with bounded octad code and coordinate lookups. -/
def generatedAxisGlobalPreferredShortMaskFast : GriessShortIndex → ℕ
  | Sum.inl p => generatedAxisGlobalShortMask (Sum.inl p)
  | Sum.inr (Sum.inl (j,e)) => generatedAxisGlobalSourceMaskJoin
      (Nat.xor (generatedAxisGlobalPreferredMaskOctadCode j).val
        (generatedAxisGlobalOmegaMask (griessOctadOmegaCoefficient e)))
      (Nat.xor (parkerThetaMask (generatedAxisGlobalPreferredMaskOctadCode j).val)
        (generatedAxisGlobalCocodeMask (generatedAxisGlobalPreferredMaskOctadNegative j e)))
  | Sum.inr (Sum.inr p) => generatedAxisGlobalShortMask (Sum.inr (Sum.inr p))

/-- Complete original catalogue certificates make the bounded formula the actual original mask. -/
theorem generatedAxisGlobalPreferredShortMaskFast_sound
    (hc : ∀ j : Fin 759, generatedAxisGlobalPreferredMaskOctadCode j =
      generatedAxisGlobalOctadCodeData j)
    (hv : ∀ (j : Fin 759) (k : Fin 8), generatedAxisGlobalPreferredMaskOctadCoordinate j k =
      generatedAxisGlobalOctadCoordinatesData j k)
    (r : GriessShortIndex) :
    generatedAxisGlobalPreferredShortMaskFast r = generatedAxisGlobalShortMask r := by
  rcases r with p | (⟨j,e⟩ | p)
  · rfl
  · simp only [generatedAxisGlobalPreferredShortMaskFast, generatedAxisGlobalShortMask,
      generatedAxisGlobalPreferredMaskOctadNegative, generatedAxisGlobalOctadNegativeMask]
    simp_rw [hc, hv]
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
