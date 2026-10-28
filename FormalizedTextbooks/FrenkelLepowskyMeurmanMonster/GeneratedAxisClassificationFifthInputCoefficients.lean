/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthOddRootLabels
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthInputCoefficients

/-! Exact original signs of the preferred inputs for the 64 odd-output rows.
The octad Fourier diagonal signs are retained before any spin-state binding. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

/-- The input signs include the original triality octad diagonal sign. -/
def generatedFifthOddRootInputPhase (j : Fin 64) : ZMod 2 :=
  match generatedFifthOddRootInputData j with
  | Sum.inl (s, _, _) => if s = 0 then 0 else 1
  | Sum.inr e => if trialityBitWeight8 (trialityEvenMask e) / 2 % 2 = 0 then 1 else 0

/-- Check that every recorded coordinate-pair input belongs to the selected octad. -/
def generatedFifthOddRootInputSupport (j : Fin 64) : Bool :=
  match generatedFifthOddRootInputData j with
  | Sum.inl (_, a, b) => Nat.testBit 0xcccc00 a.val && Nat.testBit 0xcccc00 b.val
  | Sum.inr _ => true

/-- All listed input pairs genuinely lie in the selected octad. -/
theorem generatedFifthOddRootInputSupport_eq : ∀ j : Fin 64,
    generatedFifthOddRootInputSupport j = true := by
  decide +kernel

/-- Each of the 64 input labels has its exact original signed coefficient. -/
theorem generatedFifth_original_input_coefficient (j : Fin 64) :
    (griessConwayEncode (sExtra (conwayShortAxis
      (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1
        (generatedFifthOddRootInputLabel j) = qSign (generatedFifthOddRootInputPhase j) := by
  have hl := generatedFifthOddRootInputData_lt j
  have hs := generatedFifthOddRootInputSupport_eq j
  unfold generatedFifthOddRootInputLabel
  split
  · rename_i s a b h
    simp only [h] at hl
    simp only [generatedFifthOddRootInputSupport, h, Bool.and_eq_true] at hs
    simpa only [generatedFifthOddRootInputPhase, h] using
      generatedFourth_original_pair_coefficient s a b hl hs.1 hs.2
  · rename_i e h
    simpa only [generatedFifthOddRootInputPhase, h] using
      generatedFourth_original_octad_coefficient e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
