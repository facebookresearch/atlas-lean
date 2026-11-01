/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite original-coordinate data for the remaining ten octad inverse-half inputs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All displayed input and output octad source codes. -/
def monsterNortonRemainingOctadUCodes : Fin 76 → Fin 4096 :=
  ![
    5, 7, 9, 16, 28, 32, 38, 48,
    58, 64, 76, 128, 138, 192, 198, 256,
    272, 284, 288, 294, 304, 314, 320, 332,
    339, 349, 384, 394, 437, 443, 448, 454,
    487, 489, 512, 768, 1024, 1055, 1071, 1087,
    1089, 1106, 1153, 1204, 1217, 1256, 1311, 1327,
    1343, 1345, 1409, 1473, 1537, 1551, 1793, 1807,
    2049, 2063, 2574, 2830, 3101, 3111, 3131, 3139,
    3205, 3273, 3342, 3357, 3367, 3387, 3395, 3420,
    3461, 3514, 3529, 3558
  ]

/-- Increasing original coordinate positions of each displayed octad. -/
def monsterNortonRemainingOctadUPositions : Fin 76 → Fin 8 → Fin 24 :=
  ![![8, 9, 10, 11, 16, 17, 18, 19],
![4, 5, 6, 7, 20, 21, 22, 23],
![8, 9, 10, 11, 20, 21, 22, 23],
![10, 11, 14, 15, 18, 19, 22, 23],
![10, 11, 14, 15, 16, 17, 20, 21],
![9, 11, 13, 15, 17, 19, 21, 23],
![9, 11, 12, 14, 16, 18, 21, 23],
![9, 10, 13, 14, 17, 18, 21, 22],
![9, 10, 12, 15, 17, 18, 20, 23],
![6, 7, 14, 15, 17, 19, 21, 22],
![6, 7, 14, 15, 16, 18, 20, 23],
![5, 7, 13, 15, 17, 18, 22, 23],
![5, 7, 12, 14, 17, 18, 20, 21],
![5, 6, 13, 14, 18, 19, 21, 23],
![5, 6, 12, 15, 16, 17, 21, 23],
![2, 3, 14, 15, 17, 18, 21, 23],
![2, 3, 10, 11, 17, 19, 21, 22],
![2, 3, 10, 11, 16, 18, 20, 23],
![2, 3, 9, 11, 13, 14, 18, 19],
![2, 3, 9, 11, 12, 15, 16, 17],
![2, 3, 9, 10, 13, 15, 22, 23],
![2, 3, 9, 10, 12, 14, 20, 21],
![2, 3, 6, 7, 18, 19, 22, 23],
![2, 3, 6, 7, 16, 17, 20, 21],
![2, 3, 6, 7, 8, 9, 12, 13],
![2, 3, 4, 5, 10, 11, 12, 13],
![2, 3, 5, 7, 13, 14, 21, 22],
![2, 3, 5, 7, 12, 15, 20, 23],
![2, 3, 5, 7, 8, 11, 16, 19],
![2, 3, 4, 6, 9, 10, 16, 19],
![2, 3, 5, 6, 13, 15, 17, 19],
![2, 3, 5, 6, 12, 14, 16, 18],
![2, 3, 4, 7, 9, 11, 20, 22],
![2, 3, 5, 6, 8, 10, 20, 22],
![1, 3, 13, 15, 18, 19, 21, 22],
![1, 2, 13, 14, 17, 19, 22, 23],
![1, 2, 3, 4, 8, 12, 16, 20],
![1, 2, 3, 4, 9, 13, 17, 21],
![1, 2, 3, 4, 10, 14, 18, 22],
![1, 2, 3, 4, 11, 15, 19, 23],
![1, 2, 3, 5, 8, 13, 18, 23],
![1, 2, 3, 5, 9, 12, 19, 22],
![1, 2, 3, 6, 8, 14, 19, 21],
![1, 2, 3, 6, 11, 13, 16, 22],
![1, 2, 3, 7, 8, 15, 17, 22],
![1, 2, 3, 7, 10, 13, 19, 20],
![1, 4, 9, 13, 14, 15, 18, 23],
![1, 4, 10, 15, 17, 21, 22, 23],
![1, 4, 11, 14, 17, 18, 19, 21],
![1, 5, 8, 13, 14, 15, 17, 21],
![1, 6, 8, 15, 17, 18, 19, 23],
![1, 7, 8, 14, 18, 21, 22, 23],
![2, 5, 6, 7, 8, 14, 17, 23],
![2, 4, 9, 10, 11, 14, 17, 23],
![3, 5, 6, 7, 8, 15, 18, 21],
![3, 4, 9, 10, 11, 15, 18, 21],
![0, 1, 2, 3, 8, 9, 10, 11],
![0, 1, 2, 3, 4, 5, 6, 7],
![0, 2, 12, 14, 16, 17, 20, 23],
![0, 3, 12, 15, 16, 18, 20, 21],
![0, 4, 9, 12, 14, 15, 17, 21],
![0, 4, 10, 14, 18, 20, 21, 23],
![0, 4, 11, 15, 16, 17, 18, 23],
![0, 5, 8, 12, 14, 15, 18, 23],
![0, 6, 8, 14, 16, 17, 18, 21],
![0, 7, 8, 15, 17, 20, 21, 23],
![0, 2, 3, 4, 8, 13, 19, 22],
![0, 2, 3, 4, 9, 12, 18, 23],
![0, 2, 3, 4, 10, 15, 17, 20],
![0, 2, 3, 4, 11, 14, 16, 21],
![0, 2, 3, 5, 8, 12, 17, 21],
![0, 2, 3, 5, 9, 13, 16, 20],
![0, 2, 3, 6, 8, 15, 16, 23],
![0, 2, 3, 6, 11, 12, 19, 20],
![0, 2, 3, 7, 8, 14, 18, 20],
![0, 2, 3, 7, 10, 12, 16, 22]]

/-- The ten remaining input source octads. -/
def monsterNortonRemainingOctadUInputChoice : Fin 10 → Fin 76 :=
  ![0, 1, 2, 3, 5, 9, 11, 15, 34, 36]

/-- The genuine family of each preferred output label. -/
def monsterNortonRemainingOctadUOutputIsOctad : Fin 10 → Fin 64 → Bool :=
  ![
    ![false, true, true, false, true, false, false, true,
    true, false, false, true, false, true, true, false,
    false, true, true, false, true, false, false, true,
    true, false, false, true, false, true, true, false,
    false, true, true, false, true, false, false, true,
    true, false, false, true, false, true, true, false,
    false, true, true, false, true, false, false, true,
    true, false, false, true, false, true, true, false
  ],
![
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false
],
![
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false
],
![
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true
],
![
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true
],
![
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true
],
![
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true
],
![
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true
],
![
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true
],
![
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false,
  false, true, true, false, true, false, false, true,
  false, true, true, false, true, false, false, true,
  true, false, false, true, false, true, true, false
]]

/-- The displayed octad-code choice for an octad output. -/
def monsterNortonRemainingOctadUOutputChoice : Fin 10 → Fin 64 → Fin 76 :=
  ![
    ![0, 34, 54, 0, 55, 0, 0, 59,
    59, 0, 0, 55, 0, 54, 34, 0,
    0, 35, 52, 0, 53, 0, 0, 58,
    58, 0, 0, 53, 0, 52, 35, 0,
    0, 34, 54, 0, 55, 0, 0, 59,
    59, 0, 0, 55, 0, 54, 34, 0,
    0, 34, 54, 0, 55, 0, 0, 59,
    59, 0, 0, 55, 0, 54, 34, 0
  ],
![
  0, 35, 52, 0, 53, 0, 0, 58,
  58, 0, 0, 53, 0, 52, 35, 0,
  0, 34, 54, 0, 55, 0, 0, 59,
  59, 0, 0, 55, 0, 54, 34, 0,
  0, 35, 52, 0, 53, 0, 0, 58,
  58, 0, 0, 53, 0, 52, 35, 0,
  0, 35, 52, 0, 53, 0, 0, 58,
  58, 0, 0, 53, 0, 52, 35, 0
],
![
  0, 35, 52, 0, 53, 0, 0, 58,
  58, 0, 0, 53, 0, 52, 35, 0,
  0, 34, 54, 0, 55, 0, 0, 59,
  59, 0, 0, 55, 0, 54, 34, 0,
  0, 35, 52, 0, 53, 0, 0, 58,
  58, 0, 0, 53, 0, 52, 35, 0,
  0, 35, 52, 0, 53, 0, 0, 58,
  58, 0, 0, 53, 0, 52, 35, 0
],
![
  26, 0, 0, 42, 0, 21, 69, 0,
  0, 69, 21, 0, 42, 0, 0, 26,
  11, 0, 0, 50, 0, 8, 62, 0,
  0, 62, 8, 0, 50, 0, 0, 11,
  11, 0, 0, 50, 0, 8, 62, 0,
  0, 62, 8, 0, 50, 0, 0, 11,
  11, 0, 0, 50, 0, 8, 62, 0,
  0, 62, 8, 0, 50, 0, 0, 11
],
![
  20, 0, 0, 39, 0, 27, 72, 0,
  0, 72, 27, 0, 39, 0, 0, 20,
  7, 0, 0, 48, 0, 12, 64, 0,
  0, 64, 12, 0, 48, 0, 0, 7,
  7, 0, 0, 48, 0, 12, 64, 0,
  0, 64, 12, 0, 48, 0, 0, 7,
  7, 0, 0, 48, 0, 12, 64, 0,
  0, 64, 12, 0, 48, 0, 0, 7
],
![
  30, 0, 0, 44, 0, 19, 68, 0,
  0, 68, 19, 0, 44, 0, 0, 30,
  13, 0, 0, 51, 0, 6, 61, 0,
  0, 61, 6, 0, 51, 0, 0, 13,
  13, 0, 0, 51, 0, 6, 61, 0,
  0, 61, 6, 0, 51, 0, 0, 13,
  13, 0, 0, 51, 0, 6, 61, 0,
  0, 61, 6, 0, 51, 0, 0, 13
],
![
  18, 0, 0, 38, 0, 31, 74, 0,
  0, 74, 31, 0, 38, 0, 0, 18,
  5, 0, 0, 47, 0, 14, 65, 0,
  0, 65, 14, 0, 47, 0, 0, 5,
  5, 0, 0, 47, 0, 14, 65, 0,
  0, 65, 14, 0, 47, 0, 0, 5,
  5, 0, 0, 47, 0, 14, 65, 0,
  0, 65, 14, 0, 47, 0, 0, 5
],
![
  22, 0, 0, 40, 0, 17, 67, 0,
  0, 67, 17, 0, 40, 0, 0, 22,
  9, 0, 0, 49, 0, 4, 60, 0,
  0, 60, 4, 0, 49, 0, 0, 9,
  9, 0, 0, 49, 0, 4, 60, 0,
  0, 60, 4, 0, 49, 0, 0, 9,
  9, 0, 0, 49, 0, 4, 60, 0,
  0, 60, 4, 0, 49, 0, 0, 9
],
![
  16, 0, 0, 37, 0, 23, 70, 0,
  0, 70, 23, 0, 37, 0, 0, 16,
  3, 0, 0, 46, 0, 10, 63, 0,
  0, 63, 10, 0, 46, 0, 0, 3,
  3, 0, 0, 46, 0, 10, 63, 0,
  0, 63, 10, 0, 46, 0, 0, 3,
  3, 0, 0, 46, 0, 10, 63, 0,
  0, 63, 10, 0, 46, 0, 0, 3
],
![
  0, 24, 25, 0, 71, 0, 0, 41,
  45, 0, 0, 75, 0, 32, 33, 0,
  43, 0, 0, 73, 0, 29, 28, 0,
  0, 57, 56, 0, 36, 0, 0, 66,
  66, 0, 0, 36, 0, 56, 57, 0,
  0, 28, 29, 0, 73, 0, 0, 43,
  0, 33, 32, 0, 75, 0, 0, 45,
  41, 0, 0, 71, 0, 25, 24, 0
]]

/-- The local even sign pattern of an octad output. -/
def monsterNortonRemainingOctadUOutputSign : Fin 10 → Fin 64 → Fin 64 :=
  ![
    ![0, 43, 53, 0, 51, 0, 0, 27,
    14, 0, 0, 45, 0, 43, 49, 0,
    0, 4, 10, 0, 12, 0, 0, 4,
    17, 0, 0, 18, 0, 20, 33, 0,
    0, 35, 42, 0, 44, 0, 0, 44,
    57, 0, 0, 50, 0, 52, 57, 0,
    0, 41, 11, 0, 13, 0, 0, 38,
    51, 0, 0, 19, 0, 21, 51, 0
  ],
![
  0, 60, 38, 0, 52, 0, 0, 60,
  41, 0, 0, 42, 0, 56, 25, 0,
  0, 36, 6, 0, 20, 0, 0, 20,
  1, 0, 0, 10, 0, 24, 62, 0,
  0, 11, 57, 0, 43, 0, 0, 11,
  30, 0, 0, 53, 0, 39, 46, 0,
  0, 54, 7, 0, 21, 0, 0, 54,
  35, 0, 0, 11, 0, 25, 19, 0
],
![
  0, 28, 42, 0, 44, 0, 0, 44,
  57, 0, 0, 50, 0, 52, 57, 0,
  0, 59, 10, 0, 12, 0, 0, 4,
  17, 0, 0, 18, 0, 20, 33, 0,
  0, 43, 53, 0, 51, 0, 0, 27,
  14, 0, 0, 45, 0, 43, 14, 0,
  0, 22, 11, 0, 13, 0, 0, 38,
  51, 0, 0, 19, 0, 21, 51, 0
],
![
  35, 0, 0, 25, 0, 28, 25, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  55, 0, 0, 55, 0, 55, 55, 0,
  0, 32, 48, 0, 48, 0, 0, 48,
  31, 0, 0, 31, 0, 31, 63, 0,
  0, 40, 24, 0, 24, 0, 0, 24,
  40, 0, 0, 40, 0, 40, 8, 0,
  0, 31, 47, 0, 47, 0, 0, 47
],
![
  28, 0, 0, 25, 0, 28, 25, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  8, 0, 0, 55, 0, 55, 55, 0,
  0, 32, 48, 0, 48, 0, 0, 48,
  40, 0, 0, 40, 0, 40, 8, 0,
  0, 31, 47, 0, 47, 0, 0, 16,
  32, 0, 0, 31, 0, 31, 63, 0,
  0, 40, 24, 0, 24, 0, 0, 24
],
![
  35, 0, 0, 38, 0, 28, 38, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  8, 0, 0, 40, 0, 8, 8, 0,
  0, 47, 31, 0, 47, 0, 0, 47,
  24, 0, 0, 24, 0, 40, 24, 0,
  0, 63, 63, 0, 31, 0, 0, 63,
  16, 0, 0, 48, 0, 32, 16, 0,
  0, 55, 55, 0, 55, 0, 0, 55
],
![
  35, 0, 0, 38, 0, 28, 38, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  63, 0, 0, 31, 0, 63, 63, 0,
  0, 24, 40, 0, 24, 0, 0, 24,
  55, 0, 0, 55, 0, 55, 55, 0,
  0, 16, 32, 0, 48, 0, 0, 16,
  8, 0, 0, 40, 0, 8, 8, 0,
  0, 47, 31, 0, 47, 0, 0, 47
],
![
  44, 0, 0, 57, 0, 28, 57, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  4, 0, 0, 47, 0, 59, 47, 0,
  0, 32, 40, 0, 32, 0, 0, 24,
  12, 0, 0, 48, 0, 12, 48, 0,
  0, 63, 31, 0, 63, 0, 0, 16,
  8, 0, 0, 31, 0, 55, 31, 0,
  0, 16, 36, 0, 16, 0, 0, 20
],
![
  19, 0, 0, 57, 0, 28, 57, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  12, 0, 0, 48, 0, 12, 48, 0,
  0, 63, 31, 0, 63, 0, 0, 47,
  20, 0, 0, 16, 0, 36, 16, 0,
  0, 31, 55, 0, 31, 0, 0, 55,
  24, 0, 0, 32, 0, 40, 32, 0,
  0, 47, 59, 0, 47, 0, 0, 59
],
![
  0, 46, 58, 0, 29, 0, 0, 29,
  28, 0, 0, 28, 0, 30, 54, 0,
  35, 0, 0, 35, 0, 30, 54, 0,
  0, 39, 39, 0, 60, 0, 0, 60,
  58, 0, 0, 58, 0, 43, 43, 0,
  0, 53, 29, 0, 37, 0, 0, 37,
  0, 53, 29, 0, 26, 0, 0, 26,
  27, 0, 0, 27, 0, 57, 45, 0
]]

/-- The original source code of an odd output. -/
def monsterNortonRemainingOctadUOutputOddCode : Fin 10 → Fin 64 → Fin 2048 :=
  ![
    ![948, 0, 0, 1973, 0, 1979, 698, 0,
    0, 954, 1723, 0, 1717, 0, 0, 692,
    948, 0, 0, 1973, 0, 1979, 698, 0,
    0, 954, 1723, 0, 1717, 0, 0, 692,
    692, 0, 0, 1717, 0, 1723, 954, 0,
    0, 698, 1979, 0, 1973, 0, 0, 948,
    948, 0, 0, 1973, 0, 1979, 698, 0,
    0, 954, 1723, 0, 1717, 0, 0, 692
  ],
![
  744, 0, 0, 1769, 0, 1767, 998, 0,
  0, 742, 2023, 0, 2025, 0, 0, 1000,
  744, 0, 0, 1769, 0, 1767, 998, 0,
  0, 742, 2023, 0, 2025, 0, 0, 1000,
  1000, 0, 0, 2025, 0, 2023, 742, 0,
  0, 998, 1767, 0, 1769, 0, 0, 744,
  744, 0, 0, 1769, 0, 1767, 998, 0,
  0, 742, 2023, 0, 2025, 0, 0, 1000
],
![
  692, 0, 0, 1717, 0, 1723, 954, 0,
  0, 698, 1979, 0, 1973, 0, 0, 948,
  692, 0, 0, 1717, 0, 1723, 954, 0,
  0, 698, 1979, 0, 1973, 0, 0, 948,
  948, 0, 0, 1973, 0, 1979, 698, 0,
  0, 954, 1723, 0, 1717, 0, 0, 692,
  692, 0, 0, 1717, 0, 1723, 954, 0,
  0, 698, 1979, 0, 1973, 0, 0, 948
],
![
  0, 1339, 314, 0, 1153, 0, 0, 384,
  128, 0, 0, 1409, 0, 58, 1083, 0,
  0, 1339, 314, 0, 1153, 0, 0, 384,
  128, 0, 0, 1409, 0, 58, 1083, 0,
  0, 1339, 314, 0, 1153, 0, 0, 384,
  128, 0, 0, 1409, 0, 58, 1083, 0,
  0, 1083, 58, 0, 1409, 0, 0, 128,
  384, 0, 0, 1153, 0, 314, 1339, 0
],
![
  0, 1413, 394, 0, 1087, 0, 0, 304,
  48, 0, 0, 1343, 0, 138, 1157, 0,
  0, 1413, 394, 0, 1087, 0, 0, 304,
  48, 0, 0, 1343, 0, 138, 1157, 0,
  0, 1413, 394, 0, 1087, 0, 0, 304,
  48, 0, 0, 1343, 0, 138, 1157, 0,
  0, 1157, 138, 0, 1343, 0, 0, 48,
  304, 0, 0, 1087, 0, 394, 1413, 0
],
![
  0, 1319, 294, 0, 1217, 0, 0, 448,
  192, 0, 0, 1473, 0, 38, 1063, 0,
  0, 1319, 294, 0, 1217, 0, 0, 448,
  192, 0, 0, 1473, 0, 38, 1063, 0,
  0, 1319, 294, 0, 1217, 0, 0, 448,
  192, 0, 0, 1473, 0, 38, 1063, 0,
  0, 1063, 38, 0, 1473, 0, 0, 192,
  448, 0, 0, 1217, 0, 294, 1319, 0
],
![
  0, 1481, 454, 0, 1071, 0, 0, 288,
  32, 0, 0, 1327, 0, 198, 1225, 0,
  0, 1481, 454, 0, 1071, 0, 0, 288,
  32, 0, 0, 1327, 0, 198, 1225, 0,
  0, 1481, 454, 0, 1071, 0, 0, 288,
  32, 0, 0, 1327, 0, 198, 1225, 0,
  0, 1225, 198, 0, 1327, 0, 0, 32,
  288, 0, 0, 1071, 0, 454, 1481, 0
],
![
  0, 1309, 284, 0, 1089, 0, 0, 320,
  64, 0, 0, 1345, 0, 28, 1053, 0,
  0, 1309, 284, 0, 1089, 0, 0, 320,
  64, 0, 0, 1345, 0, 28, 1053, 0,
  0, 1309, 284, 0, 1089, 0, 0, 320,
  64, 0, 0, 1345, 0, 28, 1053, 0,
  0, 1053, 28, 0, 1345, 0, 0, 64,
  320, 0, 0, 1089, 0, 284, 1309, 0
],
![
  0, 1347, 332, 0, 1055, 0, 0, 272,
  16, 0, 0, 1311, 0, 76, 1091, 0,
  0, 1347, 332, 0, 1055, 0, 0, 272,
  16, 0, 0, 1311, 0, 76, 1091, 0,
  0, 1347, 332, 0, 1055, 0, 0, 272,
  16, 0, 0, 1311, 0, 76, 1091, 0,
  0, 1091, 76, 0, 1311, 0, 0, 16,
  272, 0, 0, 1055, 0, 332, 1347, 0
],
![
  1024, 0, 0, 1294, 0, 271, 257, 0,
  0, 187, 181, 0, 1204, 0, 0, 1466,
  0, 231, 233, 0, 1256, 0, 0, 1510,
  1372, 0, 0, 1106, 0, 83, 93, 0,
  0, 349, 339, 0, 1362, 0, 0, 1116,
  1254, 0, 0, 1512, 0, 489, 487, 0,
  1210, 0, 0, 1460, 0, 437, 443, 0,
  0, 1, 15, 0, 1038, 0, 0, 1280
]]

/-- The distinguished original coordinate of an odd output. -/
def monsterNortonRemainingOctadUOutputOddPosition : Fin 10 → Fin 64 → Fin 24 :=
  ![
    ![3, 0, 0, 3, 0, 3, 3, 0,
    0, 3, 3, 0, 3, 0, 0, 3,
    15, 0, 0, 15, 0, 15, 15, 0,
    0, 15, 15, 0, 15, 0, 0, 15,
    18, 0, 0, 18, 0, 18, 18, 0,
    0, 18, 18, 0, 18, 0, 0, 18,
    21, 0, 0, 21, 0, 21, 21, 0,
    0, 21, 21, 0, 21, 0, 0, 21
  ],
![
  2, 0, 0, 2, 0, 2, 2, 0,
  0, 2, 2, 0, 2, 0, 0, 2,
  23, 0, 0, 23, 0, 23, 23, 0,
  0, 23, 23, 0, 23, 0, 0, 23,
  17, 0, 0, 17, 0, 17, 17, 0,
  0, 17, 17, 0, 17, 0, 0, 17,
  14, 0, 0, 14, 0, 14, 14, 0,
  0, 14, 14, 0, 14, 0, 0, 14
],
![
  2, 0, 0, 2, 0, 2, 2, 0,
  0, 2, 2, 0, 2, 0, 0, 2,
  23, 0, 0, 23, 0, 23, 23, 0,
  0, 23, 23, 0, 23, 0, 0, 23,
  17, 0, 0, 17, 0, 17, 17, 0,
  0, 17, 17, 0, 17, 0, 0, 17,
  14, 0, 0, 14, 0, 14, 14, 0,
  0, 14, 14, 0, 14, 0, 0, 14
],
![
  0, 23, 23, 0, 23, 0, 0, 23,
  23, 0, 0, 23, 0, 23, 23, 0,
  0, 15, 15, 0, 15, 0, 0, 15,
  15, 0, 0, 15, 0, 15, 15, 0,
  0, 18, 18, 0, 18, 0, 0, 18,
  18, 0, 0, 18, 0, 18, 18, 0,
  0, 17, 17, 0, 17, 0, 0, 17,
  17, 0, 0, 17, 0, 17, 17, 0
],
![
  0, 14, 14, 0, 14, 0, 0, 14,
  14, 0, 0, 14, 0, 14, 14, 0,
  0, 21, 21, 0, 21, 0, 0, 21,
  21, 0, 0, 21, 0, 21, 21, 0,
  0, 18, 18, 0, 18, 0, 0, 18,
  18, 0, 0, 18, 0, 18, 18, 0,
  0, 17, 17, 0, 17, 0, 0, 17,
  17, 0, 0, 17, 0, 17, 17, 0
],
![
  0, 14, 14, 0, 14, 0, 0, 14,
  14, 0, 0, 14, 0, 14, 14, 0,
  0, 21, 21, 0, 21, 0, 0, 21,
  21, 0, 0, 21, 0, 21, 21, 0,
  0, 18, 18, 0, 18, 0, 0, 18,
  18, 0, 0, 18, 0, 18, 18, 0,
  0, 23, 23, 0, 23, 0, 0, 23,
  23, 0, 0, 23, 0, 23, 23, 0
],
![
  0, 23, 23, 0, 23, 0, 0, 23,
  23, 0, 0, 23, 0, 23, 23, 0,
  0, 21, 21, 0, 21, 0, 0, 21,
  21, 0, 0, 21, 0, 21, 21, 0,
  0, 15, 15, 0, 15, 0, 0, 15,
  15, 0, 0, 15, 0, 15, 15, 0,
  0, 17, 17, 0, 17, 0, 0, 17,
  17, 0, 0, 17, 0, 17, 17, 0
],
![
  0, 14, 14, 0, 14, 0, 0, 14,
  14, 0, 0, 14, 0, 14, 14, 0,
  0, 21, 21, 0, 21, 0, 0, 21,
  21, 0, 0, 21, 0, 21, 21, 0,
  0, 15, 15, 0, 15, 0, 0, 15,
  15, 0, 0, 15, 0, 15, 15, 0,
  0, 17, 17, 0, 17, 0, 0, 17,
  17, 0, 0, 17, 0, 17, 17, 0
],
![
  0, 14, 14, 0, 14, 0, 0, 14,
  14, 0, 0, 14, 0, 14, 14, 0,
  0, 15, 15, 0, 15, 0, 0, 15,
  15, 0, 0, 15, 0, 15, 15, 0,
  0, 18, 18, 0, 18, 0, 0, 18,
  18, 0, 0, 18, 0, 18, 18, 0,
  0, 23, 23, 0, 23, 0, 0, 23,
  23, 0, 0, 23, 0, 23, 23, 0
],
![
  13, 0, 0, 12, 0, 9, 5, 0,
  0, 7, 10, 0, 20, 0, 0, 22,
  0, 6, 11, 0, 16, 0, 0, 19,
  1, 0, 0, 0, 0, 4, 8, 0,
  0, 8, 4, 0, 0, 0, 0, 1,
  19, 0, 0, 16, 0, 11, 6, 0,
  22, 0, 0, 20, 0, 10, 7, 0,
  0, 5, 9, 0, 12, 0, 0, 13
]]

/-- The complete preferred central output phase. -/
def monsterNortonRemainingOctadUPhase : Fin 10 → Fin 64 → ZMod 2 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0
  ],
![
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0
],
![
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0
],
![
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0
],
![
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0
],
![
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0
],
![
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0
],
![
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0
],
![
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0
],
![
  0, 1, 1, 1, 1, 1, 1, 0,
  1, 1, 1, 0, 1, 0, 0, 0,
  1, 1, 1, 0, 1, 0, 0, 0,
  1, 0, 0, 0, 0, 0, 0, 1,
  1, 1, 1, 0, 1, 0, 0, 0,
  1, 0, 0, 0, 0, 0, 0, 1,
  1, 0, 0, 0, 0, 0, 0, 1,
  0, 0, 0, 1, 0, 1, 1, 1
]]

/-- Each displayed source code is a genuine weight-eight Golay word. -/
theorem monsterNortonRemainingOctadUCodes_weight (c : Fin 76) :
    golayMaskWeight (golayEncodedMask (monsterNortonRemainingOctadUCodes c).val) = 8 := by
  revert c
  decide +kernel

/-- Every displayed coordinate belongs to its source octad. -/
theorem monsterNortonRemainingOctadUPositions_mem (c : Fin 76) (i : Fin 8) :
    (golayEncodedMask (monsterNortonRemainingOctadUCodes c).val).testBit
      (monsterNortonRemainingOctadUPositions c i).val = true := by
  revert c i
  decide +kernel

/-- The coordinate table is strictly increasing in the original physical ordering. -/
theorem monsterNortonRemainingOctadUPositions_strictMono (c : Fin 76) :
    StrictMono (monsterNortonRemainingOctadUPositions c) := by
  intro i j h
  have hc : ∀ c : Fin 76, ∀ i j : Fin 8, i < j →
      monsterNortonRemainingOctadUPositions c i < monsterNortonRemainingOctadUPositions c j := by
    decide +kernel
  exact hc c i j h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
