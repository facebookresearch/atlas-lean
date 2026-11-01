/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinMaskLetters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan1Blocks

/-! Exact integer row certificates retain every original phase in this bounded word block. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete original signed input model of this bounded block. -/
def generatedFifthPermutationMask1Input3 : generatedFifthSpinMaskRows :=
  ⟨fun i => ((![
        912, 390, 1652, 1660, 523, 1936,
        512, 1280, 234, 312, 123, 2078
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        529, 1266, 992, 1032, 880, 224,
        0, 512, 1280, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩

/-- Original signed intermediate rows and literal transpose/product certificates. -/
def generatedFifthPermutationMask1Block3 : List (generatedFifthSpinMaskStep (Fin 2 × Bool)) :=
  [
    ((1, true),
      ⟨fun i => ((![
        466, 234, 1370, 1362, 871, 252,
        1838, 1582, 390, 534, 115, 2078
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        319, 1100, 380, 464, 1600, 576,
        320, 1792, 768, 512, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1040, 3346, 2062, 3864, 3629, 1804,
        1292, 291, 675, 125, 172, 2048
      ],
      ![
        809, 1881, 1807, 1328, 423, 1692,
        1660, 1080, 978, 1751, 1660, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        1792, 1719, 1277, 1771, 710, 570,
        161, 1679, 1654, 172, 417, 3328
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        801, 254, 1096, 1048, 224, 64,
        192, 0, 1024, 0, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1040, 4063, 3056, 2278, 3629, 1266,
        1087, 291, 349, 720, 204, 2048
      ],
      ![
        319, 1463, 793, 1275, 1445, 584,
        734, 1288, 150, 101, 1430, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        949, 409, 597, 761, 1127, 1629,
        143, 1536, 3, 1696, 1697, 3087
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1663, 252, 1496, 464, 16, 1760,
        1152, 256, 0, 1536, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1230, 442, 918, 684, 294, 1902,
        284, 1758, 3073, 443, 2447, 2048
      ],
      ![
        965, 693, 1360, 2023, 89, 425,
        562, 325, 33, 1642, 105, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        1699, 3, 1753, 1653, 1533, 672,
        356, 652, 409, 556, 1549, 3087
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1165, 160, 164, 168, 672, 352,
        704, 384, 0, 1024, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3455, 2384, 2165, 2154, 47, 1561,
        60, 1611, 3, 1709, 3760, 2048
      ],
      ![
        1193, 252, 791, 874, 710, 1141,
        218, 1932, 44, 204, 1696, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        1679, 1154, 312, 788, 1363, 2035,
        838, 458, 97, 225, 174, 2048
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        545, 1570, 1280, 1800, 176, 64,
        512, 1792, 512, 0, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3359, 2051, 3800, 3988, 284, 633,
        92, 437, 336, 1709, 3101, 2048
      ],
      ![
        219, 131, 144, 1257, 1749, 475,
        1177, 367, 556, 1243, 726, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        182, 1510, 453, 292, 882, 1153,
        1197, 1383, 1092, 81, 1569, 2683
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1107, 1362, 228, 1280, 1008, 1984,
        1088, 1536, 768, 512, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        817, 1267, 1097, 1157, 60, 1828,
        1008, 1699, 252, 105, 51, 2048
      ],
      ![
        287, 1950, 1943, 83, 1404, 1220,
        591, 1554, 1837, 630, 349, 0
      ]),
    ((0, true),
      ⟨fun i => ((![
        336, 1696, 738, 691, 1509, 356,
        1885, 570, 12, 267, 1687, 2971
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        331, 1348, 416, 1504, 480, 64,
        192, 0, 768, 512, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3812, 2195, 463, 2112, 2577, 3291,
        2966, 103, 158, 3088, 1506, 2048
      ],
      ![
        447, 1236, 497, 1280, 1255, 1353,
        333, 1099, 882, 512, 176, 0
      ]),
    ((1, true),
      ⟨fun i => ((![
        263, 12, 1049, 1096, 841, 161,
        1743, 1217, 1696, 2032, 1734, 2971
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1761, 82, 1284, 1280, 48, 1536,
        1664, 1792, 512, 0, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3672, 3724, 1392, 3008, 3273, 190,
        117, 3102, 2673, 3278, 1106, 2048
      ],
      ![
        331, 2043, 428, 1255, 1328, 591,
        1960, 527, 1755, 3, 439, 0
      ])
  ]

/-- Integer decoding gives the exact original signed input model. -/
theorem generatedFifth_permutation_mask1_input3 :
    generatedFifthSpinMaskRowsModel generatedFifthPermutationMask1Input3 =
      generatedFifthPermutationPlan1Input3 := by
  rfl

/-- The decoded mask plan is the complete original literal matrix plan. -/
theorem generatedFifth_permutation_mask1_block3 :
    generatedFifthSpinMaskPlan generatedFifthPermutationMask1Block3 =
      generatedFifthPermutationPlan1Block3 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
