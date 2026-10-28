/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinMaskLetters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan3Blocks

/-! Exact integer row certificates retain every original phase in this bounded word block. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete original signed input model of this bounded block. -/
def generatedFifthPermutationMask3Input7 : generatedFifthSpinMaskRows :=
  ⟨fun i => ((![
        1092, 1220, 1061, 1366, 2034, 963,
        1935, 775, 1510, 1043, 1923, 2683
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        723, 1970, 4, 1456, 256, 1184,
        1984, 1920, 0, 512, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩

/-- Original signed intermediate rows and literal transpose/product certificates. -/
def generatedFifthPermutationMask3Block7 : List (generatedFifthSpinMaskStep (Fin 2 × Bool)) :=
  [
    ((0, true),
      ⟨fun i => ((![
        1152, 64, 1154, 145, 1077, 2038,
        1871, 1096, 92, 491, 967, 2971
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1001, 606, 704, 1216, 160, 1792,
        1664, 1920, 768, 512, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3812, 4088, 463, 2112, 2584, 2324,
        2363, 1394, 1528, 3312, 1887, 2048
      ],
      ![
        1903, 911, 2033, 1456, 302, 652,
        522, 1779, 958, 512, 1125, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        439, 92, 425, 1466, 1065, 979,
        1629, 355, 64, 1216, 2004, 2971
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        209, 1216, 1508, 1456, 1648, 352,
        1920, 1536, 0, 1536, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3672, 3684, 1392, 3008, 2360, 560,
        2018, 3629, 3680, 3168, 245, 2048
      ],
      ![
        1001, 888, 668, 1399, 279, 1719,
        956, 298, 695, 951, 758, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        775, 1771, 1999, 783, 586, 409,
        349, 62, 1153, 546, 1635, 2127
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        11, 696, 2008, 1720, 0, 480,
        768, 768, 0, 1536, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2293, 2217, 1091, 2142, 3179, 157,
        2018, 3629, 3245, 3168, 1624, 2048
      ],
      ![
        1523, 1768, 1720, 1705, 1163, 1509,
        135, 1361, 69, 704, 691, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        1699, 1153, 1, 1217, 32, 48,
        1360, 2032, 1771, 1516, 675, 2127
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1039, 1036, 1036, 1024, 1984, 1472,
        192, 128, 0, 0, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3439, 3743, 2253, 2302, 224, 1666,
        3158, 294, 109, 1567, 1286, 2048
      ],
      ![
        615, 212, 964, 967, 546, 785,
        1663, 766, 1052, 237, 1407, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        355, 466, 182, 1370, 1056, 1040,
        1696, 336, 512, 256, 1024, 2048
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1073, 1360, 1508, 8, 352, 960,
        448, 768, 256, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3343, 3329, 2560, 2816, 224, 1969,
        3016, 1931, 704, 1409, 971, 2048
      ],
      ![
        1919, 189, 1711, 847, 1984, 978,
        719, 1810, 1871, 349, 914, 0
      ])
  ]

/-- Integer decoding gives the exact original signed input model. -/
theorem generatedFifth_permutation_mask3_input7 :
    generatedFifthSpinMaskRowsModel generatedFifthPermutationMask3Input7 =
      generatedFifthPermutationPlan3Input7 := by
  rfl

/-- The decoded mask plan is the complete original literal matrix plan. -/
theorem generatedFifth_permutation_mask3_block7 :
    generatedFifthSpinMaskPlan generatedFifthPermutationMask3Block7 =
      generatedFifthPermutationPlan3Block7 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
