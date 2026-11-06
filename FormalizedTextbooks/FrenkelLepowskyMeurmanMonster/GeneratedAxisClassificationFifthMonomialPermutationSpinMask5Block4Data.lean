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
def generatedFifthPermutationMask5Input4 : generatedFifthSpinMaskRows :=
  ⟨fun i => ((![
        936, 1898, 1000, 252, 1822, 713,
        1615, 1582, 1370, 1516, 1286, 2487
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1158, 1122, 1388, 1048, 32, 544,
        1152, 1664, 512, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩

/-- Original signed intermediate rows and literal transpose/product certificates. -/
def generatedFifthPermutationMask5Block4 : List (generatedFifthSpinMaskStep (Fin 2 × Bool)) :=
  [
    ((1, false),
      ⟨fun i => ((![
        182, 1370, 710, 466, 1326, 2007,
        79, 1792, 1898, 1218, 1554, 2487
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1944, 1044, 288, 616, 352, 288,
        1984, 0, 512, 0, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2144, 3538, 3800, 1023, 2328, 2703,
        878, 2605, 3863, 247, 2002, 2048
      ],
      ![
        1072, 240, 1498, 1309, 1484, 1663,
        238, 791, 1769, 233, 382, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        1280, 263, 1310, 768, 828, 761,
        274, 1871, 1942, 788, 786, 3083
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1944, 878, 1888, 792, 544, 544,
        1216, 1536, 1792, 512, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2144, 3967, 2165, 338, 3115, 2321,
        878, 2605, 2490, 1444, 1970, 2048
      ],
      ![
        0, 66, 58, 783, 973, 690,
        724, 1329, 1943, 711, 1093, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        664, 1744, 122, 864, 46, 453,
        1117, 1629, 901, 1566, 394, 3087
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        798, 1020, 1260, 2032, 592, 1408,
        768, 256, 1024, 512, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2210, 3526, 918, 2228, 1908, 48,
        160, 288, 2015, 1976, 2437, 2048
      ],
      ![
        632, 1393, 1255, 1446, 1688, 1857,
        1593, 1842, 577, 1962, 978, 0
      ]),
    ((1, false),
      ⟨fun i => ((![
        1435, 901, 556, 310, 1403, 912,
        267, 1035, 1744, 1096, 656, 3087
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1096, 104, 1792, 1688, 384, 1248,
        704, 1024, 768, 1024, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2528, 3604, 3056, 3797, 711, 28,
        238, 1315, 1320, 907, 2754, 2048
      ],
      ![
        1280, 156, 754, 1273, 358, 254,
        95, 342, 1925, 1096, 1444, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        1648, 613, 597, 806, 2027, 1771,
        1691, 1280, 1456, 794, 1248, 3069
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        815, 1838, 668, 1376, 2016, 1984,
        64, 512, 256, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2259, 2265, 2062, 2773, 1337, 28,
        784, 1315, 123, 1318, 2961, 2048
      ],
      ![
        683, 1458, 1951, 466, 1674, 408,
        1008, 1355, 1493, 1250, 428, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        1259, 501, 469, 1508, 779, 256,
        480, 923, 409, 371, 11, 2255
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        292, 156, 1256, 112, 304, 992,
        0, 128, 1280, 0, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2166, 632, 2062, 2672, 2885, 3387,
        3127, 3440, 2968, 2687, 1521, 2048
      ],
      ![
        1726, 1353, 394, 193, 507, 1900,
        1814, 1211, 1863, 1345, 743, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        1179, 1822, 1127, 1277, 768, 523,
        912, 635, 16, 1073, 1168, 2191
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1051, 1152, 4, 1152, 496, 896,
        128, 0, 256, 0, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3991, 3729, 2062, 3473, 902, 587,
        2639, 2511, 1022, 144, 9, 2048
      ],
      ![
        1475, 1320, 300, 1207, 793, 1182,
        657, 19, 295, 112, 32, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        1057, 16, 979, 841, 1038, 5,
        292, 1487, 1822, 901, 1034, 2191
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        416, 682, 224, 568, 1808, 32,
        1856, 384, 1280, 0, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2733, 2215, 2062, 2219, 1995, 652,
        140, 3145, 82, 242, 1551, 2048
      ],
      ![
        1366, 1463, 1155, 330, 27, 1901,
        1133, 385, 378, 122, 311, 0
      ])
  ]

/-- Integer decoding gives the exact original signed input model. -/
theorem generatedFifth_permutation_mask5_input4 :
    generatedFifthSpinMaskRowsModel generatedFifthPermutationMask5Input4 =
      generatedFifthPermutationPlan5Input4 := by
  rfl

/-- The decoded mask plan is the complete original literal matrix plan. -/
theorem generatedFifth_permutation_mask5_block4 :
    generatedFifthSpinMaskPlan generatedFifthPermutationMask5Block4 =
      generatedFifthPermutationPlan5Block4 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
