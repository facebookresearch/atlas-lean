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
def generatedFifthPermutationMask3Input3 : generatedFifthSpinMaskRows :=
  ⟨fun i => ((![
        1648, 1660, 692, 581, 624, 1771,
        1536, 1280, 81, 664, 379, 3069
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        49, 242, 1792, 264, 1680, 64,
        1600, 896, 512, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩

/-- Original signed intermediate rows and literal transpose/product certificates. -/
def generatedFifthPermutationMask3Block3 : List (generatedFifthSpinMaskStep (Fin 2 × Bool)) :=
  [
    ((0, true),
      ⟨fun i => ((![
        1435, 519, 1615, 1239, 1403, 912,
        1035, 267, 691, 425, 1803, 3087
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        598, 1222, 668, 2040, 352, 1984,
        0, 1664, 0, 0, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3368, 1056, 2062, 3618, 3863, 3127,
        3387, 2596, 3200, 2687, 227, 2048
      ],
      ![
        50, 618, 1631, 538, 1568, 395,
        1213, 462, 152, 1203, 766, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        1792, 1031, 30, 439, 2027, 1147,
        1936, 1691, 1699, 1696, 656, 2110
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        687, 1052, 1432, 1696, 1424, 1248,
        704, 128, 1280, 512, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        4063, 3551, 2062, 3797, 313, 784,
        28, 809, 1713, 1318, 3165, 2048
      ],
      ![
        439, 44, 1608, 1121, 535, 354,
        1612, 764, 1845, 1949, 1650, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        3, 1699, 1465, 1040, 1359, 564,
        1756, 828, 1031, 775, 825, 2110
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1475, 448, 1796, 1712, 384, 1376,
        704, 1024, 768, 1536, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        442, 2494, 2062, 2228, 3308, 2872,
        48, 2008, 89, 2001, 1011, 2048
      ],
      ![
        1853, 57, 1821, 439, 647, 1251,
        707, 1571, 1850, 1689, 1288, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        664, 738, 1615, 980, 1654, 1915,
        5, 1504, 1456, 425, 417, 3087
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        913, 176, 0, 224, 1392, 352,
        0, 1408, 256, 1536, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1815, 2835, 3056, 3284, 3308, 3238,
        80, 70, 1684, 1762, 350, 2048
      ],
      ![
        1139, 1881, 624, 482, 340, 1911,
        1671, 1731, 1419, 743, 1907, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        1648, 214, 692, 581, 2007, 269,
        1089, 1509, 1975, 1435, 2001, 3069
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        637, 342, 372, 840, 1056, 1728,
        1280, 1792, 1280, 1024, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3684, 2102, 2140, 2597, 313, 1970,
        190, 1931, 1960, 63, 2484, 2048
      ],
      ![
        1851, 1583, 1261, 878, 582, 1498,
        1299, 1540, 1447, 1074, 1047, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        270, 1965, 1117, 271, 6, 1754,
        564, 420, 1743, 241, 1759, 2094
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1854, 664, 552, 1096, 1920, 96,
        768, 1024, 768, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        4088, 786, 2494, 2592, 3863, 2437,
        3291, 3990, 4016, 3357, 2001, 2048
      ],
      ![
        64, 1117, 675, 605, 841, 289,
        947, 86, 289, 267, 667, 0
      ]),
    ((1, false),
      ⟨fun i => ((![
        1598, 1743, 527, 1885, 356, 600,
        390, 2038, 1965, 1699, 909, 2094
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1855, 1432, 1228, 672, 1056, 1344,
        384, 0, 1024, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1806, 3385, 3551, 3375, 1636, 2754,
        1828, 1954, 139, 1378, 1318, 2048
      ],
      ![
        371, 24, 1765, 133, 64, 284,
        1073, 834, 1730, 1421, 115, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        912, 692, 214, 1653, 1239, 1679,
        963, 1077, 1639, 1691, 1459, 2127
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1612, 2042, 448, 1216, 1440, 736,
        1088, 128, 0, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1806, 2759, 3551, 3375, 169, 2961,
        186, 1986, 1496, 1967, 907, 2048
      ],
      ![
        1456, 314, 345, 1845, 525, 1273,
        203, 1759, 25, 1211, 242, 0
      ])
  ]

/-- Integer decoding gives the exact original signed input model. -/
theorem generatedFifth_permutation_mask3_input3 :
    generatedFifthSpinMaskRowsModel generatedFifthPermutationMask3Input3 =
      generatedFifthPermutationPlan3Input3 := by
  rfl

/-- The decoded mask plan is the complete original literal matrix plan. -/
theorem generatedFifth_permutation_mask3_block3 :
    generatedFifthSpinMaskPlan generatedFifthPermutationMask3Block3 =
      generatedFifthPermutationPlan3Block3 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
