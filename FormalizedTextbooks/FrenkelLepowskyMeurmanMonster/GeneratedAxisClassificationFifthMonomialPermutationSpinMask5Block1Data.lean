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
def generatedFifthPermutationMask5Input1 : generatedFifthSpinMaskRows :=
  ⟨fun i => ((![
        949, 761, 597, 409, 519, 1533,
        1359, 512, 1699, 1696, 609, 2255
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1662, 252, 1500, 472, 0, 800,
        512, 512, 1792, 512, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩

/-- Original signed intermediate rows and literal transpose/product certificates. -/
def generatedFifthPermutationMask5Block1 : List (generatedFifthSpinMaskStep (Fin 2 × Bool)) :=
  [
    ((0, false),
      ⟨fun i => ((![
        768, 1239, 1885, 2027, 102, 2042,
        97, 1871, 214, 972, 353, 2048
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        544, 1086, 1164, 208, 240, 64,
        192, 128, 1280, 0, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3455, 2384, 2165, 2154, 47, 1827,
        3174, 2859, 105, 1943, 864, 2048
      ],
      ![
        730, 455, 1908, 935, 1439, 31,
        127, 711, 1822, 1420, 530, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        946, 298, 154, 818, 263, 1948,
        1582, 1838, 806, 182, 723, 2078
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        318, 76, 1400, 472, 1072, 1440,
        64, 1280, 0, 1536, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1230, 442, 918, 684, 294, 1144,
        2046, 810, 1709, 685, 174, 2048
      ],
      ![
        1568, 1893, 1305, 1611, 793, 1462,
        68, 520, 1691, 923, 923, 0
      ]),
    ((1, false),
      ⟨fun i => ((![
        912, 806, 692, 284, 779, 1936,
        1536, 1280, 298, 664, 379, 2078
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        784, 1874, 740, 1632, 1024, 256,
        64, 1920, 512, 512, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1040, 4063, 3056, 2278, 3629, 971,
        1024, 1573, 443, 1513, 224, 2048
      ],
      ![
        392, 230, 1486, 1861, 387, 1678,
        64, 179, 190, 935, 182, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        946, 298, 154, 818, 263, 1948,
        1582, 1838, 806, 182, 723, 2078
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        318, 76, 1400, 472, 1072, 1440,
        64, 1280, 0, 1536, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1040, 3346, 2062, 3864, 3629, 1286,
        1024, 549, 1467, 631, 224, 2048
      ],
      ![
        392, 505, 1995, 1272, 183, 1071,
        64, 823, 42, 644, 664, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        768, 1239, 1885, 2027, 102, 2042,
        97, 1871, 214, 972, 353, 2048
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        544, 1086, 1164, 208, 240, 64,
        192, 128, 1280, 0, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1040, 4063, 3056, 2278, 3629, 971,
        1024, 1573, 443, 1513, 224, 2048
      ],
      ![
        318, 1207, 1821, 499, 981, 728,
        64, 742, 1309, 181, 0, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        949, 761, 597, 409, 519, 1533,
        1359, 512, 1699, 1696, 609, 2255
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1662, 252, 1500, 472, 0, 800,
        512, 512, 1792, 512, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1230, 442, 918, 684, 294, 1144,
        2046, 810, 1709, 685, 174, 2048
      ],
      ![
        1540, 885, 1588, 1775, 809, 1981,
        1413, 1382, 990, 1758, 2024, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        3, 1699, 1465, 1653, 1629, 672,
        420, 1516, 761, 332, 429, 2255
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        748, 1792, 1376, 512, 880, 768,
        576, 384, 768, 1024, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3455, 2384, 2165, 2154, 47, 1827,
        3174, 2859, 105, 1943, 864, 2048
      ],
      ![
        1544, 252, 1747, 674, 118, 719,
        227, 1007, 822, 1238, 1027, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        1871, 738, 664, 980, 2035, 1363,
        1510, 10, 161, 1057, 430, 3328
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        800, 386, 4, 352, 1376, 1120,
        1216, 256, 0, 1536, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3359, 2051, 3800, 3988, 284, 1518,
        2968, 3558, 1732, 314, 158, 2048
      ],
      ![
        1050, 387, 404, 1665, 773, 185,
        2040, 1580, 1741, 985, 1977, 0
      ])
  ]

/-- Integer decoding gives the exact original signed input model. -/
theorem generatedFifth_permutation_mask5_input1 :
    generatedFifthSpinMaskRowsModel generatedFifthPermutationMask5Input1 =
      generatedFifthPermutationPlan5Input1 := by
  rfl

/-- The decoded mask plan is the complete original literal matrix plan. -/
theorem generatedFifth_permutation_mask5_block1 :
    generatedFifthSpinMaskPlan generatedFifthPermutationMask5Block1 =
      generatedFifthPermutationPlan5Block1 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
