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
def generatedFifthPermutationMask5Input0 : generatedFifthSpinMaskRows :=
  generatedFifthSpinMaskIdentity

/-- Original signed intermediate rows and literal transpose/product certificates. -/
def generatedFifthPermutationMask5Block0 : List (generatedFifthSpinMaskStep (Fin 2 × Bool)) :=
  [
    ((0, false),
      ⟨fun i => ((![
        241, 1075, 355, 659, 1040, 48,
        1152, 192, 779, 12, 1265, 3069
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1038, 14, 1032, 1032, 880, 928,
        960, 896, 1536, 1024, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        1, 2, 4, 8, 16, 32,
        64, 128, 256, 512, 1024, 2048
      ],
      ![
        1038, 14, 1032, 1032, 880, 928,
        960, 896, 1536, 1024, 0, 0
      ]),
    ((1, false),
      ⟨fun i => ((![
        775, 779, 1453, 1629, 808, 841,
        1039, 1038, 1075, 1218, 1793, 3069
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        184, 110, 1132, 1120, 656, 1376,
        1600, 384, 0, 0, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3343, 270, 2560, 2816, 3131, 3111,
        3205, 3273, 2308, 2312, 1106, 2048
      ],
      ![
        1304, 1342, 1028, 1028, 1010, 445,
        1662, 1185, 1171, 1024, 1955, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        871, 1900, 889, 1000, 1065, 97,
        783, 1, 1696, 1008, 1126, 2971
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        2016, 2034, 0, 1896, 896, 32,
        0, 896, 1792, 1024, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3439, 963, 2253, 2302, 2312, 2324,
        2600, 2564, 3127, 3131, 1996, 2048
      ],
      ![
        828, 1954, 1945, 957, 15, 864,
        1963, 2013, 1396, 1396, 1229, 0
      ]),
    ((1, false),
      ⟨fun i => ((![
        1360, 1696, 1154, 1043, 1509, 420,
        1277, 2042, 1900, 1035, 1271, 2971
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        394, 740, 708, 840, 48, 1248,
        64, 768, 0, 0, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        2293, 3137, 1091, 2142, 2564, 1855,
        1583, 2824, 2639, 2895, 1298, 2048
      ],
      ![
        1766, 1772, 421, 1083, 920, 1853,
        1261, 112, 1725, 1469, 1867, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        534, 838, 453, 1508, 274, 1089,
        781, 775, 1156, 145, 1761, 2683
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1842, 1586, 1504, 1896, 128, 32,
        704, 896, 1024, 1536, 0, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3672, 3724, 1392, 3008, 3273, 1522,
        1489, 3318, 2481, 2434, 2015, 2048
      ],
      ![
        1570, 654, 1210, 958, 1775, 50,
        1372, 1994, 69, 592, 986, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        1871, 738, 664, 980, 2035, 1363,
        1510, 10, 161, 1057, 430, 3328
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        800, 386, 4, 352, 1376, 1120,
        1216, 256, 0, 1536, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3812, 2195, 463, 2112, 2577, 3080,
        3118, 1804, 222, 3267, 1320, 2048
      ],
      ![
        648, 1418, 1660, 887, 1452, 805,
        1780, 785, 545, 1004, 1574, 0
      ]),
    ((0, false),
      ⟨fun i => ((![
        3, 1699, 1465, 1653, 1629, 672,
        420, 1516, 761, 332, 429, 2255
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        748, 1792, 1376, 512, 880, 768,
        576, 384, 768, 1024, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        817, 1267, 1097, 1157, 60, 1874,
        123, 1374, 3193, 31, 2673, 2048
      ],
      ![
        1822, 2005, 274, 1424, 1919, 325,
        1127, 1419, 777, 1128, 1245, 0
      ]),
    ((1, false),
      ⟨fun i => ((![
        949, 761, 597, 409, 519, 1533,
        1359, 512, 1699, 1696, 609, 2255
      ] : Fin 12 → Fin 4096) i).val,
      fun i => ((![
        1662, 252, 1500, 472, 0, 800,
        512, 512, 1792, 512, 1024, 0
      ] : Fin 12 → Fin 4096) i).val⟩,
      ![
        3359, 2051, 3800, 3988, 284, 1518,
        2968, 3558, 1732, 314, 158, 2048
      ],
      ![
        1160, 1629, 1749, 1676, 1097, 483,
        185, 867, 1932, 623, 1050, 0
      ])
  ]

/-- Integer decoding gives the exact original signed input model. -/
theorem generatedFifth_permutation_mask5_input0 :
    generatedFifthSpinMaskRowsModel generatedFifthPermutationMask5Input0 =
      generatedFifthPermutationPlan5Input0 := by
  exact generatedFifth_spin_mask_identity

/-- The decoded mask plan is the complete original literal matrix plan. -/
theorem generatedFifth_permutation_mask5_block0 :
    generatedFifthSpinMaskPlan generatedFifthPermutationMask5Block0 =
      generatedFifthPermutationPlan5Block0 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
