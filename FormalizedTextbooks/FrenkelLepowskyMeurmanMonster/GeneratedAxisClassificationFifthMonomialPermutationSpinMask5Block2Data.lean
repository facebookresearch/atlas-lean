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
def generatedFifthPermutationMask5Input2 : generatedFifthSpinMaskRows :=
  ⟨fun i => ((![
        1871, 738, 664, 980, 2035, 1363,
        1510, 10, 161, 1057, 430, 3328
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        800, 386, 4, 352, 1376, 1120,
        1216, 256, 0, 1536, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩

/-- Original signed intermediate rows and literal transpose/product certificates. -/
def generatedFifthPermutationMask5Block2 : List (generatedFifthSpinMaskStep (Fin 2 × Bool)) :=
  [
    ((0, true),
      ⟨fun i => ((![
        534, 838, 453, 1508, 274, 1089,
        781, 775, 1156, 145, 1761, 2683
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1842, 1586, 1504, 1896, 128, 32,
        704, 896, 1024, 1536, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        817, 1267, 1097, 1157, 60, 1874,
        123, 1374, 3193, 31, 2673, 2048
      ],
      ![
        286, 862, 243, 827, 1996, 163,
        346, 736, 1238, 593, 543, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        1045, 1156, 4, 1061, 1744, 1753,
        1942, 710, 838, 336, 704, 2683
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        591, 1068, 1180, 1208, 1072, 160,
        576, 512, 1024, 1536, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3812, 2195, 463, 2112, 2577, 3080,
        3118, 1804, 222, 3267, 1320, 2048
      ],
      ![
        583, 1592, 14, 2041, 1398, 32,
        728, 1636, 1048, 1546, 1156, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        332, 600, 664, 1495, 1040, 9,
        6, 1360, 1698, 1057, 908, 3328
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1150, 1982, 376, 688, 464, 704,
        1088, 128, 0, 0, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2089, 2496, 463, 2080, 2673, 2056,
        4016, 1266, 832, 3568, 123, 2048
      ],
      ![
        198, 42, 602, 689, 83, 1605,
        64, 1715, 534, 390, 1251, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        3, 1153, 1465, 1653, 1948, 1049,
        1756, 1366, 1088, 1871, 911, 2255
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        477, 156, 676, 40, 128, 96,
        1088, 1280, 768, 0, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        552, 328, 1097, 1063, 158, 768,
        139, 1292, 3209, 1286, 2968, 2048
      ],
      ![
        1651, 413, 1645, 189, 1416, 1761,
        1604, 1837, 1811, 1249, 1845, 0
      ]),
    ((1, false),
      ⟨fun i => ((![
        783, 1088, 1652, 1464, 1885, 1566,
        2007, 1691, 1153, 1154, 67, 2255
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        788, 602, 536, 848, 848, 896,
        1536, 1024, 768, 512, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3631, 3713, 3800, 3700, 252, 12,
        3016, 3158, 1684, 1624, 1022, 2048
      ],
      ![
        160, 214, 427, 1362, 1781, 1557,
        0, 1079, 309, 1871, 632, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        768, 1615, 519, 523, 1822, 323,
        1752, 332, 756, 972, 835, 2048
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        272, 82, 1704, 1064, 144, 64,
        1152, 1408, 1024, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3537, 3809, 2165, 2233, 252, 12,
        3158, 3016, 89, 245, 1022, 2048
      ],
      ![
        346, 647, 1906, 493, 662, 896,
        943, 686, 1772, 498, 712, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        713, 81, 32, 209, 1117, 1629,
        527, 1940, 1660, 12, 394, 3069
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1870, 174, 156, 1072, 0, 256,
        576, 896, 1024, 512, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1070, 1086, 918, 730, 336, 256,
        2018, 832, 1713, 1887, 82, 2048
      ],
      ![
        1636, 1691, 934, 1797, 1806, 207,
        1760, 224, 701, 926, 338, 0
      ]),
    ((1, false),
      ⟨fun i => ((![
        1648, 1660, 692, 581, 624, 1771,
        1536, 1280, 81, 664, 379, 3069
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        49, 242, 1792, 264, 1680, 64,
        1600, 896, 512, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2171, 1088, 3056, 3953, 2490, 2308,
        2363, 3209, 3200, 2529, 432, 2048
      ],
      ![
        65, 162, 144, 1032, 1847, 465,
        1347, 948, 636, 1092, 12, 0
      ])
  ]

/-- Integer decoding gives the exact original signed input model. -/
theorem generatedFifth_permutation_mask5_input2 :
    generatedFifthSpinMaskRowsModel generatedFifthPermutationMask5Input2 =
      generatedFifthPermutationPlan5Input2 := by
  rfl

/-- The decoded mask plan is the complete original literal matrix plan. -/
theorem generatedFifth_permutation_mask5_block2 :
    generatedFifthSpinMaskPlan generatedFifthPermutationMask5Block2 =
      generatedFifthPermutationPlan5Block2 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
