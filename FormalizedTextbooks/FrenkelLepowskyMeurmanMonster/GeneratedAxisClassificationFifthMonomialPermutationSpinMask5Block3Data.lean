/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinMaskLetters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan5Blocks

/-! Exact integer row certificates retain every original phase in this bounded word block. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete original signed input model of this bounded block. -/
def generatedFifthPermutationMask5Input3 : generatedFifthSpinMaskRows :=
  ⟨fun i => ((![
        1648, 1660, 692, 581, 624, 1771,
        1536, 1280, 81, 664, 379, 3069
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        49, 242, 1792, 264, 1680, 64,
        1600, 896, 512, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩

/-- Original signed intermediate rows and literal transpose/product certificates. -/
def generatedFifthPermutationMask5Block3 : List (generatedFifthSpinMaskStep (Fin 2 × Bool)) :=
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
    ((1, true),
      ⟨fun i => ((![
        794, 691, 122, 738, 1487, 292,
        62, 1854, 519, 1948, 1427, 3087
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        16, 616, 368, 528, 976, 544,
        1216, 1536, 0, 512, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        4063, 3551, 2062, 3797, 313, 784,
        28, 809, 1713, 1318, 3165, 2048
      ],
      ![
        552, 1208, 1848, 1781, 1299, 1641,
        1406, 858, 1728, 1815, 958, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        1280, 30, 1031, 923, 838, 610,
        393, 1719, 1679, 525, 1673, 3083
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        778, 1158, 1892, 1264, 432, 1024,
        640, 768, 256, 1536, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3346, 3551, 3056, 2773, 1735, 238,
        28, 1562, 1713, 907, 3728, 2048
      ],
      ![
        1300, 3, 895, 933, 253, 1088,
        56, 578, 408, 585, 527, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        469, 32, 1598, 1075, 207, 685,
        1207, 512, 1000, 161, 905, 2127
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1947, 604, 1500, 264, 896, 1664,
        384, 1152, 1792, 0, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        4044, 2494, 918, 3914, 138, 160,
        48, 1480, 89, 1976, 3461, 2048
      ],
      ![
        717, 1625, 927, 1352, 1665, 1024,
        141, 416, 977, 36, 1439, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        841, 1000, 1898, 1383, 775, 1706,
        556, 852, 32, 501, 388, 2127
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1299, 390, 240, 1776, 560, 1056,
        640, 0, 1024, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3705, 2140, 2165, 3380, 77, 878,
        2321, 1905, 1281, 1444, 76, 2048
      ],
      ![
        1877, 1647, 289, 1650, 1076, 1826,
        519, 1102, 1062, 1075, 146, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        1948, 1160, 1031, 263, 643, 1453,
        720, 376, 1043, 525, 1560, 3083
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        799, 1884, 732, 912, 528, 1696,
        384, 1280, 512, 0, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2585, 2108, 3800, 2151, 640, 878,
        2703, 1570, 1695, 247, 44, 2048
      ],
      ![
        1601, 1017, 495, 1809, 309, 182,
        1, 1098, 213, 308, 1067, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        1566, 1043, 1310, 30, 536, 1495,
        808, 97, 1160, 788, 792, 3083
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1158, 14, 800, 1648, 880, 288,
        1920, 128, 1536, 1024, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2876, 2332, 557, 3747, 1473, 160,
        192, 115, 169, 1617, 3367, 2048
      ],
      ![
        1030, 1110, 1016, 1574, 62, 1696,
        1950, 1189, 1584, 1072, 1186, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        936, 1898, 1000, 252, 1822, 713,
        1615, 1582, 1370, 1516, 1286, 2487
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1158, 1122, 1388, 1048, 32, 544,
        1152, 1664, 512, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2210, 2095, 557, 3421, 1599, 192,
        160, 288, 1636, 1617, 2343, 2048
      ],
      ![
        390, 354, 1108, 540, 260, 564,
        1920, 128, 1111, 1480, 395, 0
      ])
  ]

/-- Integer decoding gives the exact original signed input model. -/
theorem generatedFifth_permutation_mask5_input3 :
    generatedFifthSpinMaskRowsModel generatedFifthPermutationMask5Input3 =
      generatedFifthPermutationPlan5Input3 := by
  rfl

/-- The decoded mask plan is the complete original literal matrix plan. -/
theorem generatedFifth_permutation_mask5_block3 :
    generatedFifthSpinMaskPlan generatedFifthPermutationMask5Block3 =
      generatedFifthPermutationPlan5Block3 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
