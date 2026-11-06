/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactFullQData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks

/-! Exact complete preferred short action by whole binary masks and central cochains. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Every complete upper triangular cocycle correction row. -/
def generatedTwelfthCompleteShortPackedRows : Fin 12 → Fin 24 → ℕ :=
  ![
    ![1536, 8388880, 8389776, 352, 8390336, 832, 8389504, 8389376, 8389120, 8389632, 8388608, 0, 0, 8388608, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0],
    ![8812296, 8800008, 17376, 8794208, 1179840, 7884608, 16649472, 15469568, 15366656, 16676864, 8798208, 8388608, 8781824, 8781824, 1179648, 0, 0, 0, 8388608, 0, 8388608, 0, 0, 0],
    ![53442, 18392, 8406896, 16576, 10331264, 12144832, 4190336, 2232320, 10318848, 10194944, 10317824, 8388608, 8404992, 8388608, 32768, 8388608, 8388608, 8388608, 8388608, 8388608, 8388608, 8388608, 0, 0],
    ![1024, 1024, 0, 0, 640, 320, 640, 256, 512, 0, 0, 0, 8388608, 8388608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1024, 1024, 0, 1024, 480, 896, 896, 512, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1024, 0, 0, 1024, 832, 704, 384, 768, 512, 0, 0, 0, 8388608, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0, 0],
    ![16, 1008, 0, 864, 512, 768, 768, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 8388608, 0, 0, 0, 0, 0],
    ![48, 672, 0, 720, 768, 256, 256, 512, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 8388608, 0, 8388608, 0, 0, 0, 0],
    ![1040, 2032, 0, 1888, 480, 896, 896, 512, 1024, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1072, 1696, 0, 1744, 480, 896, 896, 512, 0, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 256, 768, 768, 512, 512, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ]

/-- All genuine compact coordinate image central coefficients, in exact unit order. -/
def generatedTwelfthCompleteShortPackedCoefficients : Fin 12 → ℕ :=
  ![14817204, 6746714, 248631, 13496, 8405387, 53474, 394243, 9127064, 30211, 29480, 868362, 869858]

/-- The complete binary and central cache metadata for every actual compact candidate. -/
def generatedTwelfthCompleteShortPackedMetadata (g : Fin 12) : Prop :=
  (∀ j, toAdd (generatedTwelfthSpinCompactFullQCache g j).base =
    monsterCo1GeometryBinaryMaskDecode (generatedTwelfthSpinCompactBinaryColumns g j)) ∧
  (∀ j k, monsterCo1GeometryBinaryMaskDecode (generatedTwelfthCompleteShortPackedRows g j) k =
    if j < k then
      qBeta (monsterCo1GeometryBinaryMaskDecode (generatedTwelfthSpinCompactBinaryColumns g j))
        (monsterCo1GeometryBinaryMaskDecode (generatedTwelfthSpinCompactBinaryColumns g k)) +
        qBeta (Pi.single j 1) (Pi.single k 1) else 0) ∧
  (∀ j, monsterCo1GeometryBinaryMaskDecode (generatedTwelfthCompleteShortPackedCoefficients g) j =
    toAdd (generatedTwelfthSpinCompactFullQCache g j).coeff)

/-- Complete vector, central phase and signed coefficient conditions for one preferred short row. -/
def generatedTwelfthCompleteShortPackedCondition (g : Fin 12) (a : Fin 98280) : Prop :=
  let r := generatedNinthLowerSpinShortIndex a
  generatedAxisGlobalQMaskVector (generatedTwelfthSpinCompactBinaryColumns g)
      (generatedAxisGlobalShortMask r) =
    generatedAxisGlobalShortMask (generatedTwelfthCompleteShortDestination g r) ∧
  (if (generatedAxisGlobalQMaskCentral (generatedTwelfthCompleteShortPackedRows g)
    (generatedTwelfthCompleteShortPackedCoefficients g) (generatedAxisGlobalShortMask r)).testBit 0
    then (1 : ZMod 2) else 0) = generatedTwelfthCompleteShortPhase g r ∧
  nortonUIntegerSign (generatedTwelfthCompleteShortPhase g r) *
    generatedTwelfthCompleteShortInputInteger r =
      generatedTwelfthCompleteShortInputInteger (generatedTwelfthCompleteShortDestination g r)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
