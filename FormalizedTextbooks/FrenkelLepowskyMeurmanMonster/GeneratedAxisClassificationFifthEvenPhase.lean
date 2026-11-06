/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthEvenRootImages
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthInputCoefficients

/-! Full actual preferred-Q phases of the 56 original octad image rows. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The exact finite preferred-Q expression of each actual octad output. -/
def generatedFifthEvenRootQ (j : Fin 56) : Q :=
  ⟨ofAdd (leechHyperbolicInverse *ᵥ integerParity
    (monsterNortonLeechCoordinates (generatedFifthEvenRootIntegral j))), 1⟩

/-- The finite preferred-Q expression is the intrinsic actual short lift. -/
theorem generatedFifthEvenRootQ_eq (j : Fin 56) :
    generatedFifthEvenRootQ j = griessShortQ (generatedFifthEvenRootOutputLabel j) := by
  rw [← monsterNortonShortQ_eq]
  unfold monsterNortonShortQ
  rw [generatedFifthEvenRootOutputLabel_integral]
  rfl

/-- The genuine central phase of the full original inverse Q image. -/
noncomputable def generatedFifthEvenRootPhase (j : Fin 56) : ZMod 2 :=
  toAdd (generatedFifthInverseQImage (generatedFifthEvenRootQ j)).coeff

/-- The displayed phase is the actual preferred local-short conjugation phase. -/
theorem generatedFifth_even_inverse_phase (j : Fin 56) :
    localShortPhase generatedFifthLocalFiber⁻¹ (generatedFifthEvenRootOutputLabel j) =
      generatedFifthEvenRootPhase j := by
  change toAdd (spinConjugation (generatedFifthLocalFiber⁻¹).val.1
    (griessShortQ (generatedFifthEvenRootOutputLabel j))).coeff = _
  rw [← generatedFifthEvenRootQ_eq, generatedFifthInverseQImage_eq]
  rfl

/-- Every octad image row retains its actual full preferred-Q lift and central phase. -/
theorem generatedFifth_even_inverse_Q_image (j : Fin 56) :
    spinConjugation (generatedFifthLocalFiber⁻¹).val.1
        (griessShortQ (generatedFifthEvenRootOutputLabel j)) =
      qCentral (generatedFifthEvenRootPhase j) *
        griessShortQ (generatedFifthEvenRootInputLabel j) := by
  rw [griessShortQ_image, generatedFifth_even_inverse_permutation,
    generatedFifth_even_inverse_phase]

/-- Original input signs include the actual octad Fourier diagonal. -/
def generatedFifthEvenRootInputPhase (j : Fin 56) : ZMod 2 :=
  match generatedFifthEvenRootInputData j with
  | Sum.inl (s, _, _) => if s = 0 then 0 else 1
  | Sum.inr e => if trialityBitWeight8 (trialityEvenMask e) / 2 % 2 = 0 then 1 else 0

/-- A finite Boolean check of the original input-pair support. -/
def generatedFifthEvenRootInputSupport (j : Fin 56) : Bool :=
  match generatedFifthEvenRootInputData j with
  | Sum.inl (_, a, b) => Nat.testBit 0xcccc00 a.val && Nat.testBit 0xcccc00 b.val
  | Sum.inr _ => true

/-- All recorded input pairs belong to the original selected octad. -/
theorem generatedFifthEvenRootInputSupport_eq : ∀ j : Fin 56,
    generatedFifthEvenRootInputSupport j = true := by
  decide +kernel

/-- Each actual octad-image input has the original signed coefficient. -/
theorem generatedFifth_original_even_input_coefficient (j : Fin 56) :
    (griessConwayEncode (sExtra (conwayShortAxis
      (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1
        (generatedFifthEvenRootInputLabel j) = qSign (generatedFifthEvenRootInputPhase j) := by
  have hl := generatedFifthEvenRootInputData_lt j
  have hs := generatedFifthEvenRootInputSupport_eq j
  unfold generatedFifthEvenRootInputLabel
  split
  · rename_i s a b h
    simp only [h] at hl
    simp only [generatedFifthEvenRootInputSupport, h, Bool.and_eq_true] at hs
    simpa only [generatedFifthEvenRootInputPhase, h] using
      generatedFourth_original_pair_coefficient s a b hl hs.1 hs.2
  · rename_i e h
    simpa only [generatedFifthEvenRootInputPhase, h] using
      generatedFourth_original_octad_coefficient e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
