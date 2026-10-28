/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual sparse half-packet short labels and finite physical U transport data. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondUpperUData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSelectedPhaseForward

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The two short families on eight pairs and sixteen units on fourteen octads. -/
abbrev NortonSecondHalfShortIndex := (Fin 8 × Fin 2) ⊕ (Fin 14 × Fin 16)

/-- Finite storage index of each actual sparse input short unit. -/
def monsterNortonSecondHalfShortStorage : NortonSecondHalfShortIndex → Fin 240
  | Sum.inl (i, s) => ⟨2 * i.val + s.val, by omega⟩
  | Sum.inr (d, e) => ⟨16 + 16 * d.val + e.val, by omega⟩

/-- All actual pure-short inputs used by the C and octad terms of the half packet. -/
noncomputable def monsterNortonSecondHalfShortInput : NortonSecondHalfShortIndex → GriessShortIndex
  | Sum.inl (i, s) => Sum.inl (s, monsterNortonSecondHalfPairIndex i)
  | Sum.inr (d, e) => Sum.inr (Sum.inl
      (monsterNortonOctadIndex (monsterNortonSecondHalfOctadCode d)
        (monsterNortonSecondHalfOctad_weight d), monsterNortonSecondHalfOctadSign d e))

/-- Zero indicates a pair output, and one an octad output. -/
def monsterNortonSecondHalfUKind : Fin 240 → ℕ :=
  ![
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 1, 1, 0,
    1, 0, 0, 1, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 1, 1, 0,
    1, 0, 0, 1, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 1, 1, 0,
    1, 0, 0, 1, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 1, 1, 0,
    1, 0, 0, 1, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 1, 1, 0,
    1, 0, 0, 1, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 1, 1, 0,
    1, 0, 0, 1, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 1, 1, 0
  ]

/-- First sorted physical coordinate of each reached pair. -/
def monsterNortonSecondHalfUPairFirst : Fin 240 → Fin 24 :=
  ![
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 9, 4, 0, 13, 0, 0, 1,
    5, 0, 0, 6, 0, 12, 0, 0,
    0, 9, 4, 0, 13, 0, 0, 1,
    5, 0, 0, 7, 0, 12, 0, 0,
    0, 4, 10, 0, 1, 0, 0, 19,
    5, 0, 0, 6, 0, 0, 16, 0,
    0, 9, 10, 0, 0, 5, 7, 0,
    6, 0, 0, 0, 11, 0, 0, 1,
    0, 5, 7, 0, 0, 10, 9, 0,
    4, 0, 0, 1, 0, 0, 0, 8,
    0, 11, 4, 0, 0, 5, 0, 0,
    6, 0, 0, 8, 9, 0, 0, 1,
    0, 0, 7, 0, 0, 4, 11, 0,
    10, 0, 0, 1, 6, 0, 0, 8,
    0, 4, 9, 0, 1, 0, 0, 13,
    7, 0, 0, 5, 0, 0, 12, 0,
    0, 10, 4, 0, 19, 0, 0, 1,
    6, 0, 0, 5, 0, 16, 0, 0,
    0, 4, 9, 0, 1, 0, 0, 13,
    6, 0, 0, 5, 0, 0, 12, 0,
    0, 5, 0, 0, 0, 11, 4, 0,
    9, 0, 0, 1, 6, 0, 0, 8,
    0, 4, 11, 0, 0, 0, 7, 0,
    6, 0, 0, 8, 10, 0, 0, 1,
    0, 5, 7, 0, 0, 9, 10, 0,
    11, 0, 0, 1, 6, 0, 0, 0,
    0, 10, 9, 0, 0, 5, 7, 0,
    0, 0, 0, 8, 4, 0, 0, 1
  ]

/-- Second sorted physical coordinate of each reached pair. -/
def monsterNortonSecondHalfUPairSecond : Fin 240 → Fin 24 :=
  ![
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 10, 11, 1, 22, 1, 1, 19,
    7, 1, 1, 8, 1, 20, 16, 1,
    1, 11, 10, 1, 19, 1, 1, 22,
    6, 1, 1, 8, 1, 16, 20, 1,
    1, 9, 11, 1, 13, 1, 1, 22,
    8, 1, 1, 7, 1, 12, 20, 1,
    1, 13, 22, 1, 1, 12, 20, 1,
    16, 1, 1, 8, 19, 1, 1, 4,
    1, 20, 12, 1, 1, 13, 22, 1,
    19, 1, 1, 11, 6, 1, 1, 16,
    1, 13, 22, 1, 1, 16, 7, 1,
    12, 1, 1, 20, 19, 1, 1, 10,
    1, 5, 16, 1, 1, 13, 22, 1,
    19, 1, 1, 9, 20, 1, 1, 12,
    1, 10, 11, 1, 22, 1, 1, 19,
    8, 1, 1, 6, 1, 20, 16, 1,
    1, 11, 9, 1, 22, 1, 1, 13,
    7, 1, 1, 8, 1, 20, 12, 1,
    1, 11, 10, 1, 19, 1, 1, 22,
    8, 1, 1, 7, 1, 16, 20, 1,
    1, 16, 7, 1, 1, 13, 22, 1,
    19, 1, 1, 10, 12, 1, 1, 20,
    1, 13, 22, 1, 1, 5, 16, 1,
    20, 1, 1, 12, 19, 1, 1, 9,
    1, 12, 20, 1, 1, 13, 22, 1,
    19, 1, 1, 4, 16, 1, 1, 8,
    1, 13, 22, 1, 1, 20, 12, 1,
    6, 1, 1, 16, 19, 1, 1, 11
  ]

/-- The genuine preferred family of each reached pair. -/
def monsterNortonSecondHalfUPairSign : Fin 240 → Fin 2 :=
  ![
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 0, 0, 1, 1, 0,
    1, 0, 0, 1, 1, 0, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 0, 0, 1, 1, 0,
    1, 0, 0, 1, 1, 0, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 0, 0, 1, 1, 0,
    1, 0, 0, 1, 1, 0, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 0, 0, 1, 1, 0,
    1, 0, 0, 1, 1, 0, 0, 1
  ]

/-- The reached octad is source code1295 or3087. -/
def monsterNortonSecondHalfUOctadChoice : Fin 240 → Fin 2 :=
  ![
    0, 1, 1, 0, 0, 1, 1, 0,
    0, 1, 1, 0, 0, 1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    0, 0, 0, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 0, 0, 0,
    1, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 1, 0,
    0, 0, 0, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 0, 0, 0,
    1, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 1, 0,
    0, 0, 0, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 0, 0, 0,
    1, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 1, 0,
    0, 0, 0, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 0, 0, 0
  ]

/-- The original even-sign label of each reached octad unit. -/
def monsterNortonSecondHalfUOctadSign : Fin 240 → Fin 64 :=
  ![
    57, 45, 51, 39, 42, 56, 38, 52,
    13, 11, 21, 19, 30, 30, 0, 0,
    1, 0, 0, 31, 0, 18, 12, 0,
    0, 1, 31, 0, 20, 0, 0, 10,
    62, 0, 0, 32, 0, 10, 20, 0,
    0, 62, 32, 0, 24, 0, 0, 6,
    44, 0, 0, 50, 0, 11, 21, 0,
    0, 42, 52, 0, 25, 0, 0, 7,
    3, 0, 0, 16, 17, 0, 0, 4,
    0, 55, 34, 0, 0, 55, 36, 0,
    14, 0, 0, 27, 15, 0, 0, 28,
    0, 37, 54, 0, 0, 54, 35, 0,
    23, 0, 0, 26, 49, 0, 0, 58,
    0, 23, 28, 0, 0, 35, 46, 0,
    48, 0, 0, 59, 5, 0, 0, 8,
    0, 47, 34, 0, 0, 8, 3, 0,
    51, 0, 0, 45, 0, 7, 25, 0,
    0, 53, 43, 0, 19, 0, 0, 13,
    33, 0, 0, 63, 0, 6, 24, 0,
    0, 33, 63, 0, 18, 0, 0, 12,
    43, 0, 0, 53, 0, 56, 38, 0,
    0, 57, 39, 0, 44, 0, 0, 50,
    47, 0, 0, 36, 9, 0, 0, 4,
    0, 61, 48, 0, 0, 9, 2, 0,
    27, 0, 0, 22, 46, 0, 0, 37,
    0, 22, 29, 0, 0, 49, 60, 0,
    15, 0, 0, 26, 29, 0, 0, 14,
    0, 41, 58, 0, 0, 41, 60, 0,
    17, 0, 0, 2, 16, 0, 0, 5,
    0, 40, 61, 0, 0, 59, 40, 0
  ]

/-- Global representative sign of the physical Leech transport. -/
def monsterNortonSecondHalfUPhysicalSign : Fin 240 → ℤ :=
  ![
    -1, -1, -1, 1, 1, 1, 1, -1,
    -1, -1, -1, 1, -1, -1, -1, 1,
    1, 1, 1, -1, 1, 1, 1, 1,
    1, 1, -1, 1, 1, 1, 1, 1,
    -1, 1, 1, 1, 1, 1, 1, 1,
    1, -1, 1, 1, 1, 1, 1, 1,
    -1, -1, 1, 1, -1, 1, 1, -1,
    1, -1, 1, -1, 1, -1, -1, 1,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, -1, 1, 1, 1, -1, 1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1,
    -1, -1, 1, 1, -1, -1, 1, 1,
    1, -1, -1, 1, 1, 1, -1, -1,
    1, -1, -1, 1, -1, -1, 1, 1,
    1, 1, 1, -1, 1, 1, 1, 1,
    1, -1, 1, 1, 1, 1, 1, 1,
    1, -1, 1, -1, -1, 1, 1, 1,
    1, 1, -1, 1, 1, -1, 1, 1,
    1, 1, 1, -1, 1, 1, 1, 1,
    1, 1, -1, 1, 1, 1, 1, 1,
    1, -1, 1, -1, -1, -1, -1, 1,
    1, 1, -1, 1, -1, -1, 1, -1,
    -1, 1, 1, 1, 1, 1, 1, 1,
    1, -1, 1, 1, 1, 1, 1, 1,
    1, -1, -1, 1, -1, -1, 1, 1,
    1, -1, -1, 1, -1, -1, 1, 1,
    -1, 1, 1, -1, 1, -1, -1, 1,
    -1, -1, 1, 1, 1, 1, -1, -1,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, -1, 1, 1, -1, 1, 1
  ]

/-- Original preferred-Q hyperbolic binary masks of the actual inputs. -/
def monsterNortonSecondHalfShortMask : Fin 240 → ℕ :=
  ![
    5242880, 5244928, 1048576, 1050624, 4456448, 4458496, 262144, 264192,
    4259840, 4261888, 65536, 67584, 5570560, 5572608, 1376256, 1378304,
    1378307, 5507075, 1310723, 5570563, 4196355, 67587, 4259843, 3,
    6817795, 2686979, 6883331, 2621443, 3997699, 8128515, 3932163, 8194051,
    1378317, 5310477, 1114125, 5570573, 4196365, 264205, 4456461, 13,
    6424589, 2490381, 6686733, 2228237, 3604493, 7538701, 3342349, 7800845,
    67598, 4524046, 327694, 4259854, 4196366, 264206, 4456462, 14,
    4851726, 917518, 5113870, 655374, 720910, 5179406, 983054, 4917262,
    5620384, 4573856, 5360288, 4309664, 1376928, 328352, 1114784, 66208,
    1311392, 262816, 1049248, 672, 5556896, 4506272, 5292704, 4246176,
    6884003, 7932579, 7146147, 8194723, 117411, 1163939, 377507, 1428131,
    4246179, 5292707, 4506275, 5556899, 2622115, 3670691, 2884259, 3932835,
    314029, 1360557, 4246189, 5292717, 6687405, 7735981, 2228909, 3277485,
    6752941, 7801517, 2294445, 3343021, 377517, 1428141, 4309677, 5360301,
    5900974, 4852398, 1966766, 918190, 1100462, 49838, 5556910, 4506286,
    5360302, 4309678, 1428142, 377518, 1770158, 721582, 6228654, 5180078,
    65537, 5308417, 1116161, 4261889, 4194305, 1048577, 5244929, 2049,
    6422529, 3278849, 7471105, 2230273, 2295809, 7536641, 3344385, 6488065,
    1376258, 4521986, 329730, 5572610, 4194306, 1048578, 5244930, 2050,
    4849666, 1705986, 5898242, 657410, 2033666, 5177346, 985090, 6225922,
    262159, 5505039, 1312783, 4458511, 4194319, 1048591, 5244943, 2063,
    6815759, 3672079, 7864335, 2623503, 2885647, 8126479, 3934223, 7077903,
    6685345, 3541665, 6423201, 3279521, 311969, 5554849, 51873, 5294753,
    4571809, 1426081, 4311713, 1165985, 2558625, 7799457, 2296481, 7537313,
    1098402, 4244130, 1362594, 4508322, 5898914, 658082, 6161058, 920226,
    5964450, 723618, 6226594, 985762, 1165986, 4311714, 1426082, 4571810,
    1378988, 4522668, 5309100, 68268, 5622444, 379564, 1165996, 4311724,
    1362604, 4508332, 5294764, 51884, 5505708, 264876, 1051308, 4194988,
    115375, 5358255, 4571823, 1426095, 6881967, 3738287, 2951855, 8192687,
    6816431, 3672751, 2886319, 8127151, 51887, 5294767, 4508335, 1362607
  ]

/-- Parity masks in the original integral Leech basis before hyperbolic conversion. -/
def monsterNortonSecondHalfShortParity : Fin 240 → ℕ :=
  ![
    5, 4, 10, 11, 80, 81, 95, 94,
    1280, 1281, 1295, 1294, 1365, 1364, 1370, 1371,
    60202, 60970, 60964, 60196, 61055, 60287, 60273, 61041,
    61004, 60237, 60227, 60994, 60184, 60953, 60951, 60182,
    58042, 58090, 58084, 58036, 59375, 59327, 59313, 59361,
    58604, 58557, 58547, 58594, 57784, 57833, 57831, 57782,
    3230, 3278, 3264, 3216, 2462, 2510, 2496, 2448,
    2734, 2815, 2801, 2720, 4015, 4094, 4080, 4001,
    49150, 49141, 49056, 49067, 44783, 44773, 44720, 44730,
    44000, 44010, 43967, 43957, 47856, 47867, 47790, 47781,
    16630, 16636, 16553, 16547, 20948, 20959, 20874, 20865,
    21716, 21727, 21642, 21633, 17911, 17917, 17832, 17826,
    23828, 23839, 23876, 23887, 20230, 20236, 20311, 20317,
    18953, 18947, 19032, 19026, 22554, 22545, 22602, 22593,
    41233, 41243, 41280, 41290, 45872, 45883, 45920, 45931,
    46640, 46651, 46688, 46699, 42000, 42010, 42049, 42059,
    3072, 3077, 3083, 3086, 2304, 2309, 2315, 2318,
    2563, 2567, 2569, 2573, 3842, 3846, 3848, 3852,
    57892, 57889, 57903, 57898, 59249, 59252, 59258, 59263,
    58433, 58437, 58443, 58447, 57621, 57617, 57631, 57627,
    192, 197, 203, 206, 144, 149, 155, 158,
    163, 167, 169, 173, 242, 246, 248, 252,
    41449, 41453, 41398, 41394, 46075, 46078, 45989, 45984,
    46843, 46846, 46757, 46752, 42216, 42220, 42167, 42163,
    24031, 24026, 23937, 23940, 20478, 20474, 20385, 20389,
    19185, 19189, 19118, 19114, 22737, 22740, 22671, 22666,
    16384, 16388, 16465, 16469, 20753, 20756, 20801, 20804,
    21521, 21524, 21569, 21572, 17665, 17669, 17744, 17748,
    48955, 48958, 49003, 49006, 44569, 44573, 44616, 44620,
    43798, 43794, 43847, 43843, 47669, 47664, 47717, 47712
  ]

/-- Each displayed reached pair uses the actual sorted coordinate convention. -/
theorem monsterNortonSecondHalfUPair_lt (k : Fin 240) :
    monsterNortonSecondHalfUPairFirst k < monsterNortonSecondHalfUPairSecond k := by
  revert k
  decide +kernel

/-- The source codes of the only two reached octad blocks. -/
def monsterNortonSecondHalfUOctadCode : Fin 2 → Fin 4096 := ![1295, 3087]

/-- Their sorted coordinates are taken from the already proved actual source dictionaries. -/
def monsterNortonSecondHalfUOctadPositions : Fin 2 → Fin 8 → Fin 24 :=
  ![monsterNortonEvenShortFirstUOctadPositions 1,
    monsterNortonEvenShortSecondUpperUOctadPositions]

/-- Both reached source codes are genuine weight-eight Golay codewords. -/
theorem monsterNortonSecondHalfUOctad_weight (c : Fin 2) :
    golayMaskWeight (golayEncodedMask (monsterNortonSecondHalfUOctadCode c).val) = 8 := by
  revert c
  decide +kernel

/-- The two stored supports are precisely the actual increasing source octad coordinates. -/
theorem monsterNortonSecondHalfUOctad_coordinate (c : Fin 2) (j : Fin 8) :
    golayOctadCoordinate (monsterNortonOctadIndex (monsterNortonSecondHalfUOctadCode c)
      (monsterNortonSecondHalfUOctad_weight c)) j =
        monsterNortonSecondHalfUOctadPositions c j := by
  fin_cases c
  · exact monsterNortonEvenShortFirstUOctad_coordinate 1 j
  · exact monsterNortonEvenShortSecondUpperUOctad_coordinate j

/-- The actual dictionary output selected by the finite physical transport data. -/
noncomputable def monsterNortonSecondHalfShortUOutput (i : NortonSecondHalfShortIndex) :
    GriessShortIndex :=
  let k := monsterNortonSecondHalfShortStorage i
  if monsterNortonSecondHalfUKind k = 0 then
    Sum.inl (monsterNortonSecondHalfUPairSign k,
      griessPairIndex (monsterNortonSecondHalfUPairFirst k) (monsterNortonSecondHalfUPairSecond k)
        (ne_of_lt (monsterNortonSecondHalfUPair_lt k)))
  else Sum.inr (Sum.inl
    (monsterNortonOctadIndex (monsterNortonSecondHalfUOctadCode
      (monsterNortonSecondHalfUOctadChoice k))
      (monsterNortonSecondHalfUOctad_weight (monsterNortonSecondHalfUOctadChoice k)),
        monsterNortonSecondHalfUOctadSign k))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
