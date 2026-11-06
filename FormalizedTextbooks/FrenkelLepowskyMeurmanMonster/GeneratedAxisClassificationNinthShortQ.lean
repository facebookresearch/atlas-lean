/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthQImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortCoordinates

/-! Finite preferred-Q coordinates use the genuine integral Leech basis and central coefficient. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The actual preferred short lift evaluated through the denominator-eight lattice inverse. -/
def generatedNinthInputShortQ (r : generatedNinthInputShortLabel) : Q :=
  ⟨ofAdd (leechHyperbolicInverse *ᵥ integerParity
    (monsterNortonLeechCoordinates (generatedNinthInputShortIntegral r))), 1⟩

/-- The finite preferred lift has exactly the intrinsic actual short-vector label and phase. -/
theorem generatedNinthInputShortQ_actual (r : generatedNinthInputShortLabel) :
    generatedNinthInputShortQ r = griessShortQ (generatedNinthInputShortIndex r) := by
  rw [← monsterNortonShortQ_eq]
  unfold generatedNinthInputShortQ monsterNortonShortQ
  rw [generatedNinthInputShortIntegral_actual]

/-- The actual short phase is the genuine nine-factor image's central coefficient. -/
theorem generatedNinth_input_short_phase (r : generatedNinthInputShortLabel) :
    localShortPhase generatedNinthLocalFiber (generatedNinthInputShortIndex r) =
      toAdd (generatedNinthQImage (generatedNinthInputShortQ r)).coeff := by
  unfold localShortPhase
  rw [← generatedNinthInputShortQ_actual, generatedNinthQImage_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
