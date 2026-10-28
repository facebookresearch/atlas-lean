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
def generatedFifthPermutationMask3Input4 : generatedFifthSpinMaskRows :=
  ⟨fun i => ((![
        912, 692, 214, 1653, 1239, 1679,
        963, 1077, 1639, 1691, 1459, 2127
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1612, 2042, 448, 1216, 1440, 736,
        1088, 128, 0, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩

/-- Original signed intermediate rows and literal transpose/product certificates. -/
def generatedFifthPermutationMask3Block4 : List (generatedFifthSpinMaskStep (Fin 2 × Bool)) :=
  [
    ((0, true),
      ⟨fun i => ((![
        298, 818, 1789, 102, 756, 1147,
        469, 1504, 1888, 889, 1571, 2397
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        576, 418, 1508, 1000, 1024, 1216,
        1664, 1792, 512, 512, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        4088, 3956, 2494, 2592, 1695, 1418,
        2396, 1655, 1089, 875, 1976, 2048
      ],
      ![
        612, 390, 1335, 2024, 1604, 835,
        1556, 1124, 672, 688, 1064, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        177, 241, 857, 32, 1533, 390,
        828, 1756, 1031, 775, 1801, 3086
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1042, 642, 736, 1128, 16, 1536,
        512, 1152, 1536, 0, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3684, 1067, 2140, 2597, 2678, 1983,
        3068, 212, 3011, 1814, 1444, 2048
      ],
      ![
        708, 1107, 1049, 1884, 543, 716,
        551, 423, 1672, 1055, 679, 0
      ]),
    ((1, false),
      ⟨fun i => ((![
        1792, 1031, 30, 871, 267, 1915,
        624, 1435, 241, 64, 1136, 3086
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1102, 1886, 892, 72, 1744, 1888,
        1792, 1280, 1280, 0, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1815, 2848, 3056, 3284, 215, 91,
        150, 179, 1652, 1732, 3472, 2048
      ],
      ![
        1682, 1410, 487, 79, 1687, 1184,
        1843, 1319, 288, 1063, 1792, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        1691, 263, 1789, 2007, 1403, 1648,
        491, 2027, 209, 889, 747, 2397
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1749, 1150, 1144, 112, 1552, 320,
        1088, 1280, 1024, 1024, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        442, 2238, 2062, 2228, 1508, 1384,
        1896, 384, 185, 105, 3235, 2048
      ],
      ![
        989, 1002, 1026, 1173, 1494, 332,
        1372, 1050, 723, 274, 1803, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        912, 1660, 214, 1653, 1936, 779,
        1280, 1536, 995, 298, 379, 2127
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1024, 1954, 740, 512, 848, 192,
        640, 896, 1792, 512, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        4063, 1243, 2062, 3797, 2877, 1780,
        4092, 1485, 2778, 1709, 189, 2048
      ],
      ![
        2020, 778, 1109, 1474, 1236, 1031,
        1449, 1983, 857, 605, 510, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        713, 995, 1040, 691, 527, 783,
        1117, 710, 1660, 1516, 2008, 2127
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        431, 1452, 1400, 1080, 224, 864,
        960, 512, 1024, 1536, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3368, 3876, 2062, 3618, 1055, 1802,
        3342, 277, 1905, 443, 218, 2048
      ],
      ![
        2019, 564, 1449, 219, 1478, 504,
        1485, 1070, 1042, 739, 731, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        768, 1789, 263, 1259, 1822, 1041,
        906, 332, 1654, 284, 1297, 2048
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        529, 1102, 252, 160, 304, 384,
        384, 1024, 1024, 0, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2171, 2234, 3056, 3953, 1356, 778,
        4035, 1675, 1570, 1467, 1860, 2048
      ],
      ![
        1873, 958, 1868, 1760, 1654, 1862,
        1979, 806, 151, 254, 511, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        1629, 672, 806, 570, 271, 1310,
        1239, 1435, 1075, 1154, 1553, 2733
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        935, 1504, 1276, 232, 1024, 32,
        64, 256, 256, 1536, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1070, 348, 918, 730, 1842, 266,
        394, 74, 1749, 339, 1338, 2048
      ],
      ![
        1879, 1252, 46, 216, 461, 1257,
        1525, 117, 978, 1792, 1141, 0
      ])
  ]

/-- Integer decoding gives the exact original signed input model. -/
theorem generatedFifth_permutation_mask3_input4 :
    generatedFifthSpinMaskRowsModel generatedFifthPermutationMask3Input4 =
      generatedFifthPermutationPlan3Input4 := by
  rfl

/-- The decoded mask plan is the complete original literal matrix plan. -/
theorem generatedFifth_permutation_mask3_block4 :
    generatedFifthSpinMaskPlan generatedFifthPermutationMask3Block4 =
      generatedFifthPermutationPlan3Block4 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
