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
def generatedFifthPermutationMask3Input5 : generatedFifthSpinMaskRows :=
  ⟨fun i => ((![
        1629, 672, 806, 570, 271, 1310,
        1239, 1435, 1075, 1154, 1553, 2733
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        935, 1504, 1276, 232, 1024, 32,
        64, 256, 256, 1536, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩

/-- Original signed intermediate rows and literal transpose/product certificates. -/
def generatedFifthPermutationMask3Block5 : List (generatedFifthSpinMaskStep (Fin 2 × Bool)) :=
  [
    ((1, true),
      ⟨fun i => ((![
        177, 1075, 857, 581, 1948, 1049,
        828, 1508, 672, 1277, 1805, 2733
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        12, 418, 272, 1184, 208, 896,
        960, 1664, 256, 1024, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3537, 1020, 2165, 2233, 1513, 2318,
        65, 2754, 180, 3087, 2017, 2048
      ],
      ![
        552, 2010, 1865, 470, 1342, 1627,
        382, 1520, 1976, 1479, 1342, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        332, 1754, 298, 1495, 32, 1081,
        356, 1152, 402, 371, 1980, 3584
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        671, 14, 1180, 104, 1424, 320,
        256, 1280, 0, 1536, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3631, 2, 3800, 3700, 631, 3011,
        652, 2961, 1236, 3420, 1714, 2048
      ],
      ![
        1423, 190, 1700, 172, 279, 326,
        904, 1370, 513, 837, 529, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        501, 1510, 182, 453, 1744, 745,
        788, 1940, 1220, 128, 1776, 2683
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1966, 942, 376, 1376, 1296, 352,
        832, 896, 0, 512, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        552, 782, 1097, 1063, 1834, 1652,
        587, 1418, 1869, 3074, 3242, 2048
      ],
      ![
        94, 1874, 770, 1814, 735, 1775,
        1503, 1523, 49, 765, 243, 0
      ]),
    ((1, false),
      ⟨fun i => ((![
        1092, 1220, 1061, 1366, 2034, 963,
        1935, 775, 1510, 1043, 1923, 2683
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        723, 1970, 4, 1456, 256, 1184,
        1984, 1920, 0, 512, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2089, 2054, 463, 2080, 3285, 3111,
        3387, 1983, 203, 3312, 1426, 2048
      ],
      ![
        913, 1607, 46, 420, 234, 182,
        979, 1682, 147, 512, 104, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        1277, 818, 298, 102, 113, 1073,
        1156, 1160, 1059, 371, 894, 3584
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        801, 416, 1504, 184, 1360, 96,
        64, 128, 1280, 1536, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3812, 4088, 463, 2112, 2584, 2324,
        2363, 1394, 1528, 3312, 1887, 2048
      ],
      ![
        315, 1409, 920, 205, 1565, 1966,
        636, 1952, 1456, 1781, 1190, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        177, 241, 857, 581, 783, 1088,
        2038, 12, 761, 332, 975, 2733
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        829, 236, 52, 104, 1600, 1088,
        640, 1280, 1792, 0, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        817, 1806, 1097, 1157, 1587, 1855,
        1561, 193, 1542, 3074, 2529, 2048
      ],
      ![
        815, 685, 676, 888, 1325, 528,
        1202, 1284, 1816, 1150, 1632, 0
      ]),
    ((1, false),
      ⟨fun i => ((![
        949, 761, 597, 841, 263, 1359,
        1533, 256, 241, 64, 723, 2733
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        927, 92, 1496, 464, 1344, 1344,
        448, 1024, 0, 1536, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3359, 1104, 3800, 3988, 327, 2371,
        1902, 3395, 1620, 3420, 96, 2048
      ],
      ![
        1083, 236, 897, 212, 326, 259,
        868, 67, 1033, 581, 1973, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        768, 2007, 271, 267, 980, 1096,
        979, 1277, 692, 284, 467, 2048
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        289, 754, 1080, 696, 1680, 1088,
        192, 1792, 0, 1024, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3455, 1072, 2165, 2154, 1351, 2371,
        1902, 3395, 249, 3087, 96, 2048
      ],
      ![
        617, 1446, 1218, 797, 214, 332,
        727, 12, 171, 1235, 1202, 0
      ])
  ]

/-- Integer decoding gives the exact original signed input model. -/
theorem generatedFifth_permutation_mask3_input5 :
    generatedFifthSpinMaskRowsModel generatedFifthPermutationMask3Input5 =
      generatedFifthPermutationPlan3Input5 := by
  rfl

/-- The decoded mask plan is the complete original literal matrix plan. -/
theorem generatedFifth_permutation_mask3_block5 :
    generatedFifthSpinMaskPlan generatedFifthPermutationMask3Block5 =
      generatedFifthPermutationPlan3Block5 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
