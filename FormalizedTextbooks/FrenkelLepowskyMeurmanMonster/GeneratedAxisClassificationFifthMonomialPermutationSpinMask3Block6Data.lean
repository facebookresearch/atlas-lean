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
def generatedFifthPermutationMask3Input6 : generatedFifthSpinMaskRows :=
  ⟨fun i => ((![
        768, 2007, 271, 267, 980, 1096,
        979, 1277, 692, 284, 467, 2048
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        289, 754, 1080, 696, 1680, 1088,
        192, 1792, 0, 1024, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩

/-- Original signed intermediate rows and literal transpose/product certificates. -/
def generatedFifthPermutationMask3Block6 : List (generatedFifthSpinMaskStep (Fin 2 × Bool)) :=
  [
    ((0, false),
      ⟨fun i => ((![
        946, 664, 504, 738, 519, 1948,
        1326, 1838, 1652, 4, 609, 2078
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        575, 1502, 156, 464, 512, 0,
        768, 0, 1792, 512, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1230, 1102, 918, 684, 2002, 384,
        1266, 1490, 1631, 339, 162, 2048
      ],
      ![
        1313, 423, 669, 1827, 1131, 986,
        58, 1064, 865, 1661, 1947, 0
      ]),
    ((1, false),
      ⟨fun i => ((![
        1648, 1652, 214, 972, 1771, 624,
        1280, 1536, 664, 298, 379, 2078
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        785, 672, 1792, 1976, 480, 1664,
        832, 128, 1024, 1536, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1040, 2265, 3056, 2278, 2343, 1485,
        1292, 47, 229, 1467, 480, 2048
      ],
      ![
        571, 233, 152, 1327, 972, 2001,
        482, 460, 1701, 1886, 1028, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        946, 664, 504, 738, 519, 1948,
        1326, 1838, 1652, 4, 609, 2078
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        575, 1502, 156, 464, 512, 0,
        768, 0, 1792, 512, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1040, 3604, 2062, 3864, 3367, 1587,
        1087, 284, 1608, 443, 211, 2048
      ],
      ![
        571, 70, 77, 1682, 6, 1408,
        908, 614, 1322, 1944, 1578, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        768, 2007, 271, 267, 980, 1096,
        979, 1277, 692, 284, 467, 2048
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        289, 754, 1080, 696, 1680, 1088,
        192, 1792, 0, 1024, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1040, 2265, 3056, 2278, 2343, 1485,
        1292, 47, 229, 1467, 480, 2048
      ],
      ![
        575, 107, 761, 43, 1787, 1872,
        340, 1102, 225, 1199, 1028, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        949, 761, 597, 841, 263, 1359,
        1533, 256, 241, 64, 723, 2733
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        927, 92, 1496, 464, 1344, 1344,
        448, 1024, 0, 1536, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1230, 1102, 918, 684, 2002, 384,
        1266, 1490, 1631, 339, 162, 2048
      ],
      ![
        391, 840, 258, 725, 1863, 1088,
        196, 1796, 746, 1947, 1028, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        177, 241, 857, 581, 783, 1088,
        2038, 12, 761, 332, 975, 2733
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        829, 236, 52, 104, 1600, 1088,
        640, 1280, 1792, 0, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3455, 1072, 2165, 2154, 1351, 2371,
        1902, 3395, 249, 3087, 96, 2048
      ],
      ![
        1131, 237, 901, 200, 517, 332,
        913, 12, 1509, 261, 1201, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        1277, 818, 298, 102, 113, 1073,
        1156, 1160, 1059, 371, 894, 3584
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        801, 416, 1504, 184, 1360, 96,
        64, 128, 1280, 1536, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3359, 1104, 3800, 3988, 327, 2371,
        1902, 3395, 1620, 3420, 96, 2048
      ],
      ![
        153, 236, 834, 1115, 1041, 493,
        1626, 173, 819, 1861, 1356, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        1092, 1220, 1061, 1366, 2034, 963,
        1935, 775, 1510, 1043, 1923, 2683
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        723, 1970, 4, 1456, 256, 1184,
        1984, 1920, 0, 512, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        817, 1806, 1097, 1157, 1587, 1855,
        1561, 193, 1542, 3074, 2529, 2048
      ],
      ![
        1583, 574, 551, 1747, 97, 1277,
        1273, 1923, 1626, 1868, 771, 0
      ])
  ]

/-- Integer decoding gives the exact original signed input model. -/
theorem generatedFifth_permutation_mask3_input6 :
    generatedFifthSpinMaskRowsModel generatedFifthPermutationMask3Input6 =
      generatedFifthPermutationPlan3Input6 := by
  rfl

/-- The decoded mask plan is the complete original literal matrix plan. -/
theorem generatedFifth_permutation_mask3_block6 :
    generatedFifthSpinMaskPlan generatedFifthPermutationMask3Block6 =
      generatedFifthPermutationPlan3Block6 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
