/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalPairCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPairPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthShortPhysical

/-! Executable sorted pair numerators and the complete two-code-bit phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original row input of a genuine monomial spatial word. -/
def generatedSixthMonomialPairInput (k : Fin 4) (i : Fin 24) : Fin 24 :=
  sixthFrameOrbitSpatialInput (Fin.natAdd 10 (Fin.castAdd 2 k)) i

/-- The original final pair numerator evaluated on sorted physical coordinates. -/
def generatedSixthMonomialPairNumerator (s : Fin 2) (a b : Fin 24) : ℤ :=
  let i := min a b
  let j := max a b
  (if s = 0 then 1 else -1) * (generatedSixthNormEightVectorData 8 i) *
    (generatedSixthNormEightVectorData 8 j) +
    4 * (generatedSixthMiddlePairNumerator 0 i j - generatedSixthMiddlePairNumerator 1 i j)

/-- Both genuine Golay signs, with no preferred phase removed. -/
def generatedSixthMonomialPairPhase (k : Fin 4) (a b : Fin 24) : ZMod 2 :=
  golayEncoder (golayLabelCoefficients (generatedSixthMonomialMaskTranslation k)) a +
    golayEncoder (golayLabelCoefficients (generatedSixthMonomialMaskTranslation k)) b

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
