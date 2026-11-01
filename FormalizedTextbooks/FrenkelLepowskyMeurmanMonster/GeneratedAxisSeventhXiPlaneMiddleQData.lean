/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortHom

/-! Exact coordinate and central-phase data for the original seventh middle Q action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Twenty-four whole-Q states at every step of the original seven-factor word. -/
def generatedSeventhXiMiddleQData : Fin 8 → Fin 24 → Fin 3 → ℕ :=
  ![
    ![
      ![1, 0, 0],
      ![2, 0, 0],
      ![4, 0, 0],
      ![8, 0, 0],
      ![16, 0, 0],
      ![32, 0, 0],
      ![64, 0, 0],
      ![128, 0, 0],
      ![256, 0, 0],
      ![512, 0, 0],
      ![1024, 0, 0],
      ![2048, 0, 0],
      ![0, 1, 0],
      ![0, 2, 0],
      ![0, 4, 0],
      ![0, 8, 0],
      ![0, 16, 0],
      ![0, 32, 0],
      ![0, 64, 0],
      ![0, 128, 0],
      ![0, 256, 0],
      ![0, 512, 0],
      ![0, 1024, 0],
      ![0, 2048, 0]
    ],
    ![
      ![0, 14, 0],
      ![0, 13, 0],
      ![0, 11, 0],
      ![0, 7, 0],
      ![16, 0, 0],
      ![32, 0, 0],
      ![64, 0, 0],
      ![128, 0, 0],
      ![256, 0, 0],
      ![512, 0, 0],
      ![0, 2048, 0],
      ![0, 1024, 0],
      ![14, 1, 1],
      ![13, 2, 1],
      ![11, 4, 1],
      ![7, 8, 1],
      ![0, 16, 0],
      ![0, 32, 0],
      ![0, 64, 0],
      ![0, 128, 0],
      ![0, 256, 0],
      ![0, 512, 0],
      ![2048, 1024, 1],
      ![1024, 2048, 0]
    ],
    ![
      ![0, 1987, 0],
      ![0, 769, 0],
      ![0, 1617, 0],
      ![0, 1441, 0],
      ![816, 1008, 0],
      ![2593, 622, 0],
      ![960, 1008, 0],
      ![2383, 367, 0],
      ![12, 12, 0],
      ![2052, 1035, 0],
      ![0, 3069, 0],
      ![0, 1265, 0],
      ![14, 240, 0],
      ![3325, 828, 0],
      ![1791, 913, 1],
      ![1535, 865, 1],
      ![0, 1040, 0],
      ![0, 48, 0],
      ![0, 1152, 0],
      ![0, 192, 0],
      ![0, 779, 0],
      ![0, 12, 0],
      ![2048, 1265, 1],
      ![2046, 3057, 0]
    ],
    ![
      ![0, 1708, 0],
      ![0, 769, 0],
      ![0, 1087, 0],
      ![0, 1230, 0],
      ![174, 0, 0],
      ![2593, 0, 0],
      ![94, 0, 0],
      ![2383, 0, 1],
      ![12, 0, 1],
      ![3076, 1036, 0],
      ![0, 3069, 0],
      ![0, 2044, 0],
      ![1008, 0, 1],
      ![3664, 12, 1],
      ![1377, 12, 1],
      ![1439, 12, 1],
      ![0, 1310, 0],
      ![0, 81, 0],
      ![0, 1679, 0],
      ![0, 161, 0],
      ![0, 10, 0],
      ![0, 12, 0],
      ![2048, 2044, 1],
      ![2046, 3057, 1]
    ],
    ![
      ![0, 2045, 0],
      ![0, 1014, 0],
      ![0, 2019, 0],
      ![0, 1906, 0],
      ![864, 768, 1],
      ![1496, 618, 1],
      ![254, 1, 1],
      ![1087, 2034, 1],
      ![768, 768, 0],
      ![1778, 497, 0],
      ![0, 2971, 0],
      ![0, 1126, 0],
      ![2966, 1798, 0],
      ![1802, 2039, 0],
      ![494, 1633, 0],
      ![638, 1377, 0],
      ![0, 1065, 0],
      ![0, 97, 0],
      ![0, 783, 0],
      ![0, 1, 0],
      ![0, 1696, 0],
      ![0, 1008, 0],
      ![2048, 1126, 1],
      ![3174, 3936, 0]
    ],
    ![
      ![2050, 2045, 1],
      ![6, 1014, 1],
      ![2051, 2019, 0],
      ![2061, 1906, 0],
      ![864, 768, 1],
      ![474, 2669, 1],
      ![254, 0, 0],
      ![2109, 4093, 1],
      ![768, 768, 0],
      ![766, 2556, 1],
      ![1028, 2971, 0],
      ![2054, 1126, 0],
      ![2966, 768, 0],
      ![2824, 4093, 1],
      ![2542, 1632, 0],
      ![2686, 1376, 0],
      ![2057, 1065, 0],
      ![14, 97, 1],
      ![15, 783, 0],
      ![14, 1, 1],
      ![2048, 1696, 1],
      ![0, 1008, 0],
      ![2054, 102, 1],
      ![3168, 870, 0]
    ],
    ![
      ![3068, 1805, 1],
      ![2040, 769, 0],
      ![2384, 1871, 0],
      ![2720, 1838, 1],
      ![158, 1008, 1],
      ![1911, 2647, 0],
      ![768, 240, 1],
      ![2800, 4000, 0],
      ![254, 241, 0],
      ![973, 2110, 0],
      ![4, 2960, 0],
      ![4088, 1181, 1],
      ![3990, 775, 1],
      ![3318, 3846, 1],
      ![2851, 1373, 0],
      ![2893, 1709, 0],
      ![3748, 1055, 1],
      ![1008, 145, 0],
      ![348, 673, 1],
      ![1008, 1008, 0],
      ![2048, 1999, 1],
      ![0, 241, 0],
      ![4088, 145, 0],
      ![3168, 870, 0]
    ],
    ![
      ![3058, 769, 0],
      ![1022, 2822, 1],
      ![2399, 847, 1],
      ![2721, 814, 0],
      ![144, 1009, 1],
      ![1912, 607, 1],
      ![768, 240, 1],
      ![3824, 2976, 1],
      ![254, 240, 1],
      ![1985, 2108, 0],
      ![1024, 2971, 0],
      ![3058, 2202, 0],
      ![920, 3841, 1],
      ![3318, 768, 0],
      ![2850, 350, 0],
      ![2882, 687, 0],
      ![2735, 2068, 0],
      ![1022, 145, 1],
      ![350, 685, 0],
      ![1008, 1008, 0],
      ![2063, 975, 0],
      ![14, 241, 1],
      ![1022, 3222, 1],
      ![102, 3942, 1]
    ]
  ]

/-- Literal original preferred basis lift and its successors, retaining the coefficient bit. -/
def generatedSeventhXiMiddleQState (r : Fin 8) (j : Fin 24) : Q :=
  ⟨ofAdd (Fin.append
    (golayLabelCoefficients ⟨generatedSeventhXiMiddleQData r j 0 % 4096, Nat.mod_lt _ (by decide)⟩)
    (golayLabelCoefficients ⟨generatedSeventhXiMiddleQData r j 1 % 4096,
      Nat.mod_lt _ (by decide)⟩)),
    ofAdd (generatedSeventhXiMiddleQData r j 2 : ZMod 2)⟩

/-- Actual full binary action rows; the basis-step certificates bind these to the source word. -/
def generatedSeventhXiMiddleQMatrixRows : Fin 24 → ℕ :=
  ![
    1114636, 16247047, 16195846, 7803174, 5126583, 13330859,
    13544359, 4930459, 5167719, 4971243, 9888, 1173645,
    3576885, 13683758, 14008878, 1363500, 7032688, 11305944,
    12075380, 8293840, 9991327, 10269887, 12587008, 12656258
  ]

/-- Central correction rows include the diagonal preferred-basis phases. -/
def generatedSeventhXiMiddleQPhaseRows : Fin 24 → ℕ :=
  ![
    1311360, 1318914, 11366404, 12169216, 1360560, 11375584,
    49216, 9747072, 49408, 1345536, 8392704, 9703424,
    380928, 327680, 12156928, 11337728, 11010048, 1441792,
    5767168, 0, 14680064, 2097152, 4194304, 8388608
  ]

/-- The compact full binary matrix of the genuine middle Q action. -/
def generatedSeventhXiMiddleQMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  fun i j => golayBooleanCast ((generatedSeventhXiMiddleQMatrixRows i).testBit j.val)

/-- The compact quadratic correction, with all original central phases. -/
def generatedSeventhXiMiddleQPhase : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  fun i j => golayBooleanCast ((generatedSeventhXiMiddleQPhaseRows i).testBit j.val)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
