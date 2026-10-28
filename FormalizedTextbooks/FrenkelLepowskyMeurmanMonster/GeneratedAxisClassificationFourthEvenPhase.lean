/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthEvenRootImages
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthInputCoefficients

/-! Full actual preferred-Q phases of the 63 original octad image rows. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The exact finite preferred-Q expression of each actual octad output. -/
def generatedFourthEvenRootQ (j : Fin 63) : Q :=
  ⟨ofAdd (leechHyperbolicInverse *ᵥ integerParity
    (monsterNortonLeechCoordinates (generatedFourthEvenRootIntegral j))), 1⟩

/-- The finite preferred-Q expression is the intrinsic actual short lift. -/
theorem generatedFourthEvenRootQ_eq (j : Fin 63) :
    generatedFourthEvenRootQ j = griessShortQ (generatedFourthEvenRootOutputLabel j) := by
  rw [← monsterNortonShortQ_eq]
  unfold monsterNortonShortQ
  rw [generatedFourthEvenRootOutputLabel_integral]
  rfl

/-- The genuine central phase of the full original inverse Q image. -/
noncomputable def generatedFourthEvenRootPhase (j : Fin 63) : ZMod 2 :=
  toAdd (generatedFourthInverseQImage (generatedFourthEvenRootQ j)).coeff

/-- The displayed phase is the actual preferred local-short conjugation phase. -/
theorem generatedFourth_even_inverse_phase (j : Fin 63) :
    localShortPhase generatedFourthLocalFiber⁻¹ (generatedFourthEvenRootOutputLabel j) =
      generatedFourthEvenRootPhase j := by
  change toAdd (spinConjugation (generatedFourthLocalFiber⁻¹).val.1
    (griessShortQ (generatedFourthEvenRootOutputLabel j))).coeff = _
  rw [← generatedFourthEvenRootQ_eq, generatedFourthInverseQImage_eq]
  rfl

/-- Every octad image row retains its actual full preferred-Q lift and central phase. -/
theorem generatedFourth_even_inverse_Q_image (j : Fin 63) :
    spinConjugation (generatedFourthLocalFiber⁻¹).val.1
        (griessShortQ (generatedFourthEvenRootOutputLabel j)) =
      qCentral (generatedFourthEvenRootPhase j) *
        griessShortQ (generatedFourthEvenRootInputLabel j) := by
  rw [griessShortQ_image, generatedFourth_even_inverse_permutation,
    generatedFourth_even_inverse_phase]

/-- Original input signs include the actual octad Fourier diagonal. -/
def generatedFourthEvenRootInputPhase (j : Fin 63) : ZMod 2 :=
  match generatedFourthEvenRootInputData j with
  | Sum.inl (s, _, _) => if s = 0 then 0 else 1
  | Sum.inr e => if trialityBitWeight8 (trialityEvenMask e) / 2 % 2 = 0 then 1 else 0

/-- A finite Boolean check of the original input-pair support. -/
def generatedFourthEvenRootInputSupport (j : Fin 63) : Bool :=
  match generatedFourthEvenRootInputData j with
  | Sum.inl (_, a, b) => Nat.testBit 0xcccc00 a.val && Nat.testBit 0xcccc00 b.val
  | Sum.inr _ => true

/-- All recorded input pairs belong to the original selected octad. -/
theorem generatedFourthEvenRootInputSupport_eq : ∀ j : Fin 63,
    generatedFourthEvenRootInputSupport j = true := by
  decide +kernel

/-- Each actual octad-image input has the original signed coefficient. -/
theorem generatedFourth_original_even_input_coefficient (j : Fin 63) :
    (griessConwayEncode (sExtra (conwayShortAxis
      (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1
        (generatedFourthEvenRootInputLabel j) = qSign (generatedFourthEvenRootInputPhase j) := by
  have hl := generatedFourthEvenRootInputData_lt j
  have hs := generatedFourthEvenRootInputSupport_eq j
  unfold generatedFourthEvenRootInputLabel
  split
  · rename_i s a b h
    simp only [h] at hl
    simp only [generatedFourthEvenRootInputSupport, h, Bool.and_eq_true] at hs
    simpa only [generatedFourthEvenRootInputPhase, h] using
      generatedFourth_original_pair_coefficient s a b hl hs.1 hs.2
  · rename_i e h
    simpa only [generatedFourthEvenRootInputPhase, h] using
      generatedFourth_original_octad_coefficient e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
