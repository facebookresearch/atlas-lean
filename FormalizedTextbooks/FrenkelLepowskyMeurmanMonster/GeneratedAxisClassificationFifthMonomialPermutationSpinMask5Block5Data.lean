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
def generatedFifthPermutationMask5Input5 : generatedFifthSpinMaskRows :=
  ⟨fun i => ((![
        1057, 16, 979, 841, 1038, 5,
        292, 1487, 1822, 901, 1034, 2191
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        416, 682, 224, 568, 1808, 32,
        1856, 384, 1280, 0, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩

/-- Original signed intermediate rows and literal transpose/product certificates. -/
def generatedFifthPermutationMask5Block5 : List (generatedFifthSpinMaskStep (Fin 2 × Bool)) :=
  [
    ((0, true),
      ⟨fun i => ((![
        491, 469, 501, 624, 1061, 1056,
        1216, 271, 781, 1629, 43, 2683
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        447, 606, 1468, 1936, 0, 800,
        576, 768, 256, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2733, 3476, 3056, 3480, 262, 65,
        140, 2692, 972, 780, 1425, 2048
      ],
      ![
        185, 643, 1903, 1170, 1062, 944,
        582, 1574, 1929, 268, 912, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        1220, 241, 1999, 402, 1509, 453,
        1039, 1280, 10, 1696, 448, 2919
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1056, 2, 1492, 2032, 176, 1536,
        640, 1408, 1024, 1024, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3991, 3201, 918, 3969, 2574, 3133,
        2639, 71, 391, 2824, 624, 2048
      ],
      ![
        1150, 1963, 981, 1043, 1265, 394,
        1305, 1770, 1258, 238, 1654, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        1706, 10, 1370, 775, 1310, 48,
        1940, 1941, 241, 1077, 1949, 2919
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        526, 12, 1112, 1024, 32, 704,
        1536, 1792, 1280, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2166, 2380, 2165, 324, 10, 2578,
        3127, 1599, 3260, 2564, 725, 2048
      ],
      ![
        1738, 1840, 155, 194, 962, 978,
        541, 1309, 818, 1426, 335, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        271, 2, 1073, 4, 1065, 1049,
        310, 1699, 376, 128, 311, 2048
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        128, 848, 740, 184, 704, 832,
        0, 1024, 256, 512, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3976, 2079, 3800, 1047, 2036, 2849,
        2308, 1473, 3292, 3273, 1749, 2048
      ],
      ![
        796, 1788, 383, 1151, 421, 338,
        24, 783, 1431, 693, 1418, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        949, 1942, 852, 980, 1041, 8,
        1965, 270, 1975, 312, 56, 3840
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1711, 758, 1912, 272, 1104, 1248,
        128, 1920, 256, 1536, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1205, 1219, 1097, 305, 1380, 1492,
        256, 640, 1345, 128, 180, 2048
      ],
      ![
        1827, 894, 2041, 1059, 504, 120,
        128, 1463, 1307, 640, 1848, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        691, 1696, 794, 546, 1948, 1940,
        1326, 1056, 1533, 1147, 909, 3083
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        305, 662, 188, 1576, 1376, 1856,
        320, 1280, 768, 512, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        337, 386, 463, 1760, 1823, 1857,
        12, 331, 3023, 2383, 2386, 2048
      ],
      ![
        305, 630, 908, 296, 420, 838,
        594, 530, 1484, 972, 1464, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        390, 1533, 882, 586, 1217, 1216,
        1359, 1096, 1696, 1043, 693, 3083
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        129, 448, 736, 936, 880, 64,
        64, 1280, 1536, 0, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3841, 2637, 1392, 3924, 821, 971,
        768, 1331, 1396, 1087, 3058, 2048
      ],
      ![
        391, 1145, 1345, 1034, 1650, 1614,
        320, 1038, 1247, 300, 1086, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        270, 768, 269, 1310, 2034, 818,
        564, 1660, 122, 458, 819, 2094
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        14, 68, 604, 664, 1408, 1696,
        384, 1536, 1280, 512, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3666, 2637, 1091, 2250, 1542, 1286,
        254, 1331, 71, 1292, 3058, 2048
      ],
      ![
        780, 1177, 1782, 2014, 866, 1780,
        954, 278, 393, 1745, 926, 0
      ])
  ]

/-- Integer decoding gives the exact original signed input model. -/
theorem generatedFifth_permutation_mask5_input5 :
    generatedFifthSpinMaskRowsModel generatedFifthPermutationMask5Input5 =
      generatedFifthPermutationPlan5Input5 := by
  rfl

/-- The decoded mask plan is the complete original literal matrix plan. -/
theorem generatedFifth_permutation_mask5_block5 :
    generatedFifthSpinMaskPlan generatedFifthPermutationMask5Block5 =
      generatedFifthPermutationPlan5Block5 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
