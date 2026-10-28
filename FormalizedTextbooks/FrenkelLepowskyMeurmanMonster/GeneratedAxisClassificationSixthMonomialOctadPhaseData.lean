/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthOctadNegativeCharacter
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPairPhase

/-! Finite base and six-coordinate characters for the complete original preferred octad phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Displayed constant terms, certified against the original quadratic and Parker theta below. -/
def generatedSixthMonomialOctadPhaseBase : Fin 4 → Fin 231 → ZMod 2 :=
  ![
    ![
      1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1,
      0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1,
      0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1,
      0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1,
      0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0,
      1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1,
      1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0,
      1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0,
      1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1
    ],
    ![
      1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0,
      0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1,
      0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1,
      0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0,
      1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1,
      1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0,
      0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1,
      1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1,
      1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0,
      0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1
    ],
    ![
      0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1,
      0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1,
      1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1,
      0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0,
      0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1,
      0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0,
      0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1
    ],
    ![
      1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0,
      1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1,
      1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1,
      0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1,
      0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1,
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0,
      0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1,
      0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0,
      0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0,
      1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0
    ]
  ]

/-- Six-bit negative-position character masks, certified from the genuine code encoder. -/
def generatedSixthMonomialOctadPhaseCharacter : Fin 4 → Fin 231 → Fin 64 :=
  ![
    ![
      3, 0, 4, 3, 1, 4, 2, 7, 5, 6, 0, 0, 6, 2, 3, 7, 6, 31, 1, 5,
      5, 6, 22, 3, 7, 22, 2, 19, 23, 18, 6, 3, 18, 2, 3, 19, 28, 28, 7, 53,
      23, 59, 5, 62, 59, 62, 42, 5, 5, 0, 0, 20, 59, 5, 42, 24, 63, 62, 5, 17,
      21, 58, 15, 54, 58, 1, 13, 8, 4, 59, 20, 26, 53, 8, 59, 33, 21, 50, 7, 22,
      1, 7, 23, 29, 6, 3, 6, 14, 15, 7, 27, 28, 1, 9, 5, 17, 5, 23, 4, 21,
      1, 1, 42, 58, 62, 58, 25, 62, 60, 2, 56, 36, 54, 13, 4, 8, 4, 50, 58, 26,
      58, 8, 59, 53, 19, 61, 45, 37, 11, 4, 2, 55, 51, 50, 54, 14, 61, 58, 13, 26,
      7, 13, 38, 7, 49, 57, 52, 0, 11, 56, 54, 25, 50, 53, 33, 5, 5, 21, 9, 13,
      9, 26, 11, 18, 51, 36, 6, 60, 4, 9, 13, 10, 25, 37, 29, 5, 0, 9, 1, 5,
      37, 12, 31, 2, 3, 10, 6, 2, 3, 7, 6, 31, 1, 5, 5, 56, 45, 50, 10, 57,
      25, 27, 54, 62, 29, 26, 61, 6, 11, 41, 52, 15, 60, 56, 10, 39, 11, 56, 39, 26,
      56, 25, 13, 26, 9, 62, 26, 58, 1, 55, 17
    ],
    ![
      9, 9, 15, 10, 3, 12, 3, 12, 5, 5, 10, 6, 6, 0, 9, 15, 6, 0, 0, 9,
      6, 43, 51, 40, 3, 58, 9, 58, 27, 27, 34, 22, 24, 10, 43, 57, 22, 9, 10, 25,
      18, 54, 54, 43, 54, 17, 18, 23, 36, 10, 17, 22, 18, 60, 23, 57, 9, 34, 33, 37,
      30, 39, 58, 27, 58, 27, 46, 58, 23, 46, 37, 43, 0, 43, 15, 42, 57, 30, 45, 20,
      18, 53, 42, 22, 51, 18, 36, 20, 5, 53, 58, 10, 33, 45, 23, 25, 15, 25, 6, 27,
      33, 27, 29, 9, 34, 39, 27, 3, 9, 12, 5, 25, 15, 29, 34, 58, 20, 45, 20, 33,
      53, 40, 12, 40, 53, 24, 25, 39, 9, 30, 51, 10, 6, 23, 27, 15, 3, 6, 9, 46,
      17, 46, 40, 20, 36, 20, 57, 53, 40, 12, 40, 53, 30, 51, 22, 53, 5, 17, 24, 29,
      9, 5, 9, 20, 57, 42, 29, 54, 6, 43, 39, 9, 5, 34, 17, 10, 18, 43, 18, 57,
      45, 46, 10, 40, 45, 24, 30, 48, 17, 23, 25, 6, 24, 22, 54, 5, 37, 45, 10, 6,
      36, 29, 60, 17, 42, 24, 0, 0, 5, 24, 57, 45, 9, 33, 36, 22, 43, 15, 37, 60,
      29, 6, 12, 22, 10, 0, 9, 6, 5, 10, 29
    ],
    ![
      61, 5, 1, 5, 5, 0, 9, 3, 9, 3, 0, 55, 0, 14, 3, 1, 55, 59, 1, 50,
      9, 42, 58, 44, 42, 59, 28, 62, 26, 62, 59, 2, 61, 15, 62, 60, 2, 61, 58, 45,
      26, 55, 3, 3, 10, 40, 39, 43, 9, 34, 26, 34, 25, 39, 28, 62, 21, 52, 42, 35,
      35, 11, 2, 32, 7, 35, 1, 2, 30, 61, 38, 56, 3, 46, 17, 3, 58, 28, 3, 34,
      43, 10, 35, 43, 34, 26, 10, 42, 43, 11, 62, 42, 8, 42, 40, 33, 35, 39, 40, 39,
      9, 26, 33, 37, 9, 8, 62, 42, 35, 41, 43, 2, 6, 33, 6, 0, 31, 0, 41, 5,
      1, 47, 47, 2, 56, 34, 11, 3, 34, 34, 62, 34, 42, 43, 35, 14, 38, 35, 26, 3,
      39, 3, 6, 28, 10, 42, 3, 11, 44, 44, 1, 50, 33, 7, 1, 62, 33, 37, 33, 32,
      14, 38, 35, 25, 3, 6, 28, 10, 42, 3, 11, 44, 44, 7, 50, 39, 31, 0, 41, 5,
      1, 47, 47, 2, 56, 34, 31, 57, 28, 30, 8, 55, 30, 13, 62, 21, 9, 62, 47, 16,
      61, 56, 2, 22, 41, 29, 30, 38, 0, 25, 61, 44, 19, 56, 49, 7, 46, 17, 3, 57,
      28, 55, 46, 13, 14, 17, 50, 25, 58, 31, 26
    ],
    ![
      56, 3, 5, 3, 8, 7, 7, 7, 6, 15, 5, 62, 15, 3, 6, 6, 56, 36, 15, 49,
      5, 56, 32, 56, 17, 40, 40, 40, 41, 8, 32, 23, 8, 56, 41, 41, 8, 39, 8, 1,
      32, 5, 15, 41, 56, 56, 32, 6, 23, 23, 52, 32, 15, 30, 30, 32, 44, 23, 49, 23,
      23, 41, 8, 50, 56, 6, 29, 15, 50, 23, 23, 54, 54, 50, 42, 8, 41, 15, 22, 31,
      7, 7, 30, 32, 23, 52, 23, 15, 30, 6, 32, 51, 23, 49, 5, 41, 41, 41, 21, 22,
      22, 63, 41, 41, 42, 42, 3, 24, 41, 24, 41, 63, 63, 14, 31, 13, 48, 32, 56, 1,
      49, 48, 23, 32, 33, 56, 63, 62, 31, 7, 48, 32, 32, 49, 49, 48, 23, 32, 33, 8,
      14, 31, 55, 48, 32, 56, 49, 1, 48, 23, 32, 33, 50, 1, 54, 49, 30, 30, 15, 15,
      49, 54, 30, 32, 54, 8, 56, 63, 23, 30, 30, 16, 63, 63, 1, 23, 50, 29, 5, 6,
      54, 50, 53, 23, 41, 15, 56, 52, 49, 49, 23, 33, 56, 30, 50, 23, 1, 30, 16, 32,
      63, 1, 8, 6, 30, 32, 44, 32, 49, 23, 15, 49, 41, 30, 32, 54, 49, 41, 1, 32,
      6, 39, 16, 1, 50, 32, 46, 42, 1, 29, 41
    ]
  ]

/-- Executable signed bit retaining both the constant phase and all six free sign bits. -/
def generatedSixthMonomialOctadPhase (k : Fin 4) (f : Fin 231) (e : Fin 64) : ZMod 2 :=
  generatedSixthMonomialOctadPhaseBase k f +
    ∑ a : Fin 6,
      (if (generatedSixthMonomialOctadPhaseCharacter k f).val.testBit a.val then 1 else 0) *
        (if e.val.testBit a.val then 1 else 0)

set_option maxHeartbeats 20000000 in
-- Check 924 constant phases from the complete original quadratic and Parker theta.
/-- Every displayed constant is the actual preferred-Q constant phase. -/
theorem generatedSixth_monomial_octad_phase_base :
    ∀ k : Fin 4, ∀ f : Fin 231,
      monsterMonomialQuadratic (representativeMatrix (generatedSixthMonomialMaskPhaseRows k))
        (golayLabelCoefficients (generatedSixthFinalOctadCacheCode f)) +
      spinDot (golayLabelCoefficients (generatedSixthMonomialMaskTranslation k))
        (sourceWordTheta (generatedSixthFinalOctadCacheCode f)) +
      spinDot (golayLabelCoefficients (generatedSixthMonomialMaskModulation k))
        (golayLabelCoefficients (generatedSixthFinalOctadCacheCode f)) =
      generatedSixthMonomialOctadPhaseBase k f := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Check the 5,544 original encoded sign-character coefficients once.
/-- Every displayed free sign coefficient is the genuine encoded correction code. -/
theorem generatedSixth_monomial_octad_phase_character :
    ∀ k : Fin 4, ∀ f : Fin 231, ∀ a : Fin 6,
      golayEncoder (golayLabelCoefficients (generatedSixthMonomialMaskTranslation k))
        (generatedSixthMonomialOctadCoordinates f (Fin.castAdd 2 a)) +
      golayEncoder (golayLabelCoefficients (generatedSixthMonomialMaskTranslation k))
        (generatedSixthMonomialOctadCoordinates f 6) =
      (if (generatedSixthMonomialOctadPhaseCharacter k f).val.testBit a.val then 1 else 0) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
