/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinMaskLetters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan1Blocks

/-! Exact integer row certificates retain every original phase in this bounded word block. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete original signed input model of this bounded block. -/
def generatedFifthPermutationMask1Input4 : generatedFifthSpinMaskRows :=
  ⟨fun i => ((![
        263, 12, 1049, 1096, 841, 161,
        1743, 1217, 1696, 2032, 1734, 2971
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1761, 82, 1284, 1280, 48, 1536,
        1664, 1792, 512, 0, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩

/-- Original signed intermediate rows and literal transpose/product certificates. -/
def generatedFifthPermutationMask1Block4 : List (generatedFifthSpinMaskStep (Fin 2 × Bool)) :=
  [
    ((0, true),
      ⟨fun i => ((![
        1383, 523, 525, 1533, 1160, 1065,
        1487, 270, 659, 1698, 1985, 2397
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        537, 174, 1192, 104, 1920, 1536,
        320, 768, 256, 1024, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2293, 3137, 1091, 2142, 2564, 800,
        1752, 4064, 2577, 3920, 1996, 2048
      ],
      ![
        835, 1807, 520, 1401, 1033, 198,
        1377, 1590, 923, 310, 1774, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        1073, 659, 963, 1075, 1040, 48,
        128, 192, 523, 1900, 49, 2397
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1039, 14, 1036, 1024, 672, 480,
        896, 1792, 512, 512, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3439, 963, 2253, 2302, 2312, 553,
        3145, 1880, 3273, 1798, 1657, 2048
      ],
      ![
        805, 1135, 1540, 1541, 1920, 2035,
        1154, 768, 1617, 621, 1523, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        1217, 610, 1220, 936, 16, 32,
        1088, 1152, 256, 1536, 1024, 3328
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1281, 928, 1284, 616, 464, 1952,
        960, 640, 1792, 0, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3343, 270, 2560, 2816, 3131, 1577,
        2692, 198, 2564, 774, 537, 2048
      ],
      ![
        1439, 1105, 1085, 861, 1087, 190,
        978, 147, 1342, 1442, 562, 0
      ])
  ]

/-- Integer decoding gives the exact original signed input model. -/
theorem generatedFifth_permutation_mask1_input4 :
    generatedFifthSpinMaskRowsModel generatedFifthPermutationMask1Input4 =
      generatedFifthPermutationPlan1Input4 := by
  rfl

/-- The decoded mask plan is the complete original literal matrix plan. -/
theorem generatedFifth_permutation_mask1_block4 :
    generatedFifthSpinMaskPlan generatedFifthPermutationMask1Block4 =
      generatedFifthPermutationPlan1Block4 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
