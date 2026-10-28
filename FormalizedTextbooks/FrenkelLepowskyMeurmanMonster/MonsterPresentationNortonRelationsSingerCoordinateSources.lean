/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact source-code and even-cocode decompositions of the twenty-three preferred Q lifts. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerEvenCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.QCoordinateGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The eleven original source-code labels associated with the low coordinate lifts. -/
def monsterNortonSingerCoordinateCode (a : Fin 11) : Fin 4096 :=
  ⟨2 ^ a.val, by fin_cases a <;> decide⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check the full actual central coefficients as well as all twenty-four binary coordinates.
/-- Each positive low coordinate lift has this phase-correct actual source decomposition. -/
theorem monsterNortonSingerCoordinateCode_decomposition (a : Fin 11) :
    qCoordinateGenerator (Fin.castAdd 13 a) =
      sourceQCode (monsterNortonSingerCoordinateCode a) 0 *
        sourceQCocode (spinModulation (sourceQCode (monsterNortonSingerCoordinateCode a) 0)) *
          qCentral (toAdd (sourceQCode (monsterNortonSingerCoordinateCode a) 0).coeff) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (fun j : Fin 24 => toAdd (qCoordinateGenerator (Fin.castAdd 13 a)).base j) =
      (fun j : Fin 24 => toAdd (sourceQCode (monsterNortonSingerCoordinateCode a) 0 *
        sourceQCocode (spinModulation (sourceQCode (monsterNortonSingerCoordinateCode a) 0)) *
          qCentral (toAdd (sourceQCode (monsterNortonSingerCoordinateCode a) 0).coeff)).base j)
    fin_cases a <;> decide +kernel
  · apply toAdd.injective
    fin_cases a <;> decide +kernel

/-- The theta cocodes appearing in those exact decompositions are genuinely even. -/
theorem monsterNortonSingerCoordinateCode_even (a : Fin 11) :
    spinModulation (sourceQCode (monsterNortonSingerCoordinateCode a) 0) 11 = 0 := by
  fin_cases a <;> decide +kernel

/-- Every positive high coordinate below the last is the corresponding actual even cocode. -/
theorem monsterNortonSingerCoordinateCocode_decomposition (a : Fin 11) :
    qCoordinateGenerator (Fin.natAdd 12 (Fin.castAdd 1 a)) =
      sourceQCocode (Pi.single (Fin.castAdd 1 a) 1) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (fun j : Fin 24 =>
      toAdd (qCoordinateGenerator (Fin.natAdd 12 (Fin.castAdd 1 a))).base j) =
      (fun j : Fin 24 => toAdd (sourceQCocode (Pi.single (Fin.castAdd 1 a) 1)).base j)
    fin_cases a <;> decide +kernel
  · rfl

/-- The middle positive coordinate lift is the original full preferred all-one element. -/
theorem monsterNortonSingerCoordinateOmega_decomposition :
    qCoordinateGenerator 11 = sourceOmegaQ := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (Pi.single (11 : Fin 24) (1 : ZMod 2) : Fin 24 → ZMod 2) =
      Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1
    decide +kernel
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
