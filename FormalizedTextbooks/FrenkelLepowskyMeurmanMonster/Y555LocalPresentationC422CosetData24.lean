/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal chronological right-coset proof data from actual original-source consequences. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawCosetPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Exact literal coset claims and source or chronological right-context moves in this interval. -/
def y422CosetData24 : Fin 128 → Y522RawCosetCertificate :=
  ![
    ⟨[1177, 11], [1179], [
      .equation 626 true false
        []
        []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10
    ], [1165, 10], [
      .equation 4 true false
        [1177, 2]
        [0, 6, 12, 4, 14, 10],
      .prior 3071 false [0, 6, 12, 4, 14, 10],
      .equation 2 true false
        [1175, 0]
        [6, 12, 4, 14, 10],
      .prior 3070 false [6, 12, 4, 14, 10],
      .equation 17 true false
        [1173, 6]
        [12, 4, 14, 10],
      .prior 3069 false [12, 4, 14, 10],
      .equation 10 true false
        [1171, 12]
        [4, 14, 10],
      .prior 3068 false [4, 14, 10],
      .equation 6 true false
        [1169, 4]
        [14, 10],
      .prior 3067 false [14, 10],
      .equation 12 true false
        [1167, 14]
        [10],
      .prior 3066 false [10]]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14
    ], [1153, 15], [
      .prior 3073 false [2, 0, 6, 12, 4, 14],
      .equation 8 true false
        [1165, 10]
        [2, 0, 6, 12, 4, 14],
      .prior 3065 false [2, 0, 6, 12, 4, 14],
      .equation 4 true false
        [1163, 2]
        [0, 6, 12, 4, 14],
      .prior 3064 false [0, 6, 12, 4, 14],
      .equation 2 true false
        [1161, 0]
        [6, 12, 4, 14],
      .prior 3063 false [6, 12, 4, 14],
      .equation 17 true false
        [1159, 6]
        [12, 4, 14],
      .prior 3062 false [12, 4, 14],
      .equation 10 true false
        [1157, 12]
        [4, 14],
      .prior 3061 false [4, 14],
      .equation 6 true false
        [1155, 4]
        [14],
      .prior 3060 false [14],
      .equation 12 true false
        [1153, 14]
        []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4
    ], [1139], [
      .prior 3074 false [10, 2, 0, 6, 12, 4],
      .prior 3059 false [10, 2, 0, 6, 12, 4],
      .equation 8 true false
        [1151, 10]
        [2, 0, 6, 12, 4],
      .prior 3058 false [2, 0, 6, 12, 4],
      .equation 4 true false
        [1149, 2]
        [0, 6, 12, 4],
      .prior 3057 false [0, 6, 12, 4],
      .equation 2 true false
        [1147, 0]
        [6, 12, 4],
      .prior 3056 false [6, 12, 4],
      .equation 17 true false
        [1145, 6]
        [12, 4],
      .prior 3055 false [12, 4],
      .equation 10 true false
        [1143, 12]
        [4],
      .prior 3054 false [4],
      .equation 6 true false
        [1141, 4]
        [],
      .prior 3053 false []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12
    ], [1127], [
      .prior 3075 false [14, 10, 2, 0, 6, 12],
      .equation 12 true false
        [1139, 14]
        [10, 2, 0, 6, 12],
      .prior 3052 false [10, 2, 0, 6, 12],
      .equation 8 true false
        [1137, 10]
        [2, 0, 6, 12],
      .prior 3051 false [2, 0, 6, 12],
      .equation 4 true false
        [1135, 2]
        [0, 6, 12],
      .prior 3050 false [0, 6, 12],
      .equation 2 true false
        [1133, 0]
        [6, 12],
      .prior 3049 false [6, 12],
      .equation 17 true false
        [1131, 6]
        [12],
      .prior 3048 false [12],
      .equation 10 true false
        [1129, 12]
        [],
      .prior 3047 false []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12
    ], [1115, 12], [
      .prior 3076 false [
        4, 14, 10, 2, 0, 6, 12
      ],
      .equation 6 true false
        [1127, 4]
        [14, 10, 2, 0, 6, 12],
      .prior 3046 false [14, 10, 2, 0, 6, 12],
      .equation 12 true false
        [1125, 14]
        [10, 2, 0, 6, 12],
      .prior 3045 false [10, 2, 0, 6, 12],
      .equation 8 true false
        [1123, 10]
        [2, 0, 6, 12],
      .prior 3044 false [2, 0, 6, 12],
      .equation 4 true false
        [1121, 2]
        [0, 6, 12],
      .prior 3043 false [0, 6, 12],
      .equation 2 true false
        [1119, 0]
        [6, 12],
      .prior 3042 false [6, 12],
      .equation 17 true false
        [1117, 6]
        [12],
      .prior 3041 false [12]]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8
    ], [1103, 9], [
      .prior 3077 false [4, 14, 10, 2, 0, 8],
      .equation 10 true false
        [1115, 12]
        [4, 14, 10, 2, 0, 8],
      .prior 3040 false [4, 14, 10, 2, 0, 8],
      .equation 6 true false
        [1113, 4]
        [14, 10, 2, 0, 8],
      .prior 3039 false [14, 10, 2, 0, 8],
      .equation 12 true false
        [1111, 14]
        [10, 2, 0, 8],
      .prior 3038 false [10, 2, 0, 8],
      .equation 8 true false
        [1109, 10]
        [2, 0, 8],
      .prior 3037 false [2, 0, 8],
      .equation 4 true false
        [1107, 2]
        [0, 8],
      .prior 3036 false [0, 8],
      .equation 2 true false
        [1105, 0]
        [8],
      .prior 3035 false [8],
      .equation 1 true false
        [1103, 8]
        []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2
    ], [1089], [
      .prior 3078 false [6, 12, 4, 14, 10, 2],
      .prior 3034 false [6, 12, 4, 14, 10, 2],
      .equation 17 true false
        [1101, 6]
        [12, 4, 14, 10, 2],
      .prior 3033 false [12, 4, 14, 10, 2],
      .equation 10 true false
        [1099, 12]
        [4, 14, 10, 2],
      .prior 3032 false [4, 14, 10, 2],
      .equation 6 true false
        [1097, 4]
        [14, 10, 2],
      .prior 3031 false [14, 10, 2],
      .equation 12 true false
        [1095, 14]
        [10, 2],
      .prior 3030 false [10, 2],
      .equation 8 true false
        [1093, 10]
        [2],
      .prior 3029 false [2],
      .equation 4 true false
        [1091, 2]
        [],
      .prior 3028 false []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10
    ], [1077], [
      .prior 3079 false [0, 6, 12, 4, 14, 10],
      .equation 2 true false
        [1089, 0]
        [6, 12, 4, 14, 10],
      .prior 3027 false [6, 12, 4, 14, 10],
      .equation 17 true false
        [1087, 6]
        [12, 4, 14, 10],
      .prior 3026 false [12, 4, 14, 10],
      .equation 10 true false
        [1085, 12]
        [4, 14, 10],
      .prior 3025 false [4, 14, 10],
      .equation 6 true false
        [1083, 4]
        [14, 10],
      .prior 3024 false [14, 10],
      .equation 12 true false
        [1081, 14]
        [10],
      .prior 3023 false [10],
      .equation 8 true false
        [1079, 10]
        [],
      .equation 576 false false
        []
        [11],
      .equation 8 false false
        [1077]
        []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14
    ], [1065], [
      .prior 3080 false [2, 0, 6, 12, 4, 14],
      .equation 4 true false
        [1077, 2]
        [0, 6, 12, 4, 14],
      .equation 575 false false
        []
        [3, 0, 6, 12, 4, 14],
      .equation 4 false false
        [1075]
        [0, 6, 12, 4, 14],
      .equation 2 true false
        [1075, 0]
        [6, 12, 4, 14],
      .equation 574 false false
        []
        [1, 6, 12, 4, 14],
      .equation 2 false false
        [1073]
        [6, 12, 4, 14],
      .equation 17 true false
        [1073, 6]
        [12, 4, 14],
      .equation 573 false false
        []
        [7, 12, 4, 14],
      .equation 17 false false
        [1071]
        [12, 4, 14],
      .equation 10 true false
        [1071, 12]
        [4, 14],
      .equation 572 false false
        []
        [13, 4, 14],
      .equation 10 false false
        [1069]
        [4, 14],
      .equation 6 true false
        [1069, 4]
        [14],
      .equation 571 false false
        []
        [5, 14],
      .equation 6 false false
        [1067]
        [14],
      .equation 12 true false
        [1067, 14]
        [],
      .equation 570 false false
        []
        [15],
      .equation 12 false false
        [1065]
        []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4
    ], [1053], [
      .prior 3081 false [10, 2, 0, 6, 12, 4],
      .equation 8 true false
        [1065, 10]
        [2, 0, 6, 12, 4],
      .equation 569 false false
        []
        [11, 2, 0, 6, 12, 4],
      .equation 8 false false
        [1063]
        [2, 0, 6, 12, 4],
      .equation 4 true false
        [1063, 2]
        [0, 6, 12, 4],
      .equation 568 false false
        []
        [3, 0, 6, 12, 4],
      .equation 4 false false
        [1061]
        [0, 6, 12, 4],
      .equation 2 true false
        [1061, 0]
        [6, 12, 4],
      .equation 567 false false
        []
        [1, 6, 12, 4],
      .equation 2 false false
        [1059]
        [6, 12, 4],
      .equation 17 true false
        [1059, 6]
        [12, 4],
      .equation 566 false false
        []
        [7, 12, 4],
      .equation 17 false false
        [1057]
        [12, 4],
      .equation 10 true false
        [1057, 12]
        [4],
      .equation 565 false false
        []
        [13, 4],
      .equation 10 false false
        [1055]
        [4],
      .equation 6 true false
        [1055, 4]
        [],
      .equation 564 false false
        []
        [5],
      .equation 6 false false
        [1053]
        []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12
    ], [1041], [
      .prior 3082 false [14, 10, 2, 0, 6, 12],
      .equation 12 true false
        [1053, 14]
        [10, 2, 0, 6, 12],
      .equation 563 false false
        []
        [15, 10, 2, 0, 6, 12],
      .equation 12 false false
        [1051]
        [10, 2, 0, 6, 12],
      .equation 8 true false
        [1051, 10]
        [2, 0, 6, 12],
      .equation 562 false false
        []
        [11, 2, 0, 6, 12],
      .equation 8 false false
        [1049]
        [2, 0, 6, 12],
      .equation 4 true false
        [1049, 2]
        [0, 6, 12],
      .equation 561 false false
        []
        [3, 0, 6, 12],
      .equation 4 false false
        [1047]
        [0, 6, 12],
      .equation 2 true false
        [1047, 0]
        [6, 12],
      .equation 560 false false
        []
        [1, 6, 12],
      .equation 2 false false
        [1045]
        [6, 12],
      .equation 17 true false
        [1045, 6]
        [12],
      .equation 559 false false
        []
        [7, 12],
      .equation 17 false false
        [1043]
        [12],
      .equation 10 true false
        [1043, 12]
        [],
      .equation 558 false false
        []
        [13],
      .equation 10 false false
        [1041]
        []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6
    ], [1029], [
      .prior 3083 false [4, 14, 10, 2, 0, 6],
      .equation 6 true false
        [1041, 4]
        [14, 10, 2, 0, 6],
      .equation 557 false false
        []
        [5, 14, 10, 2, 0, 6],
      .equation 6 false false
        [1039]
        [14, 10, 2, 0, 6],
      .equation 12 true false
        [1039, 14]
        [10, 2, 0, 6],
      .equation 556 false false
        []
        [15, 10, 2, 0, 6],
      .equation 12 false false
        [1037]
        [10, 2, 0, 6],
      .equation 8 true false
        [1037, 10]
        [2, 0, 6],
      .equation 555 false false
        []
        [11, 2, 0, 6],
      .equation 8 false false
        [1035]
        [2, 0, 6],
      .equation 4 true false
        [1035, 2]
        [0, 6],
      .equation 554 false false
        []
        [3, 0, 6],
      .equation 4 false false
        [1033]
        [0, 6],
      .equation 2 true false
        [1033, 0]
        [6],
      .equation 553 false false
        []
        [1, 6],
      .equation 2 false false
        [1031]
        [6],
      .equation 17 true false
        [1031, 6]
        [],
      .equation 552 false false
        []
        [7],
      .equation 17 false false
        [1029]
        []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0
    ], [375], [
      .prior 3084 false [12, 4, 14, 10, 2, 0],
      .equation 10 true false
        [1029, 12]
        [4, 14, 10, 2, 0],
      .equation 551 false false
        []
        [13, 4, 14, 10, 2, 0],
      .equation 10 false false
        [1027]
        [4, 14, 10, 2, 0],
      .equation 6 true false
        [1027, 4]
        [14, 10, 2, 0],
      .equation 550 false false
        []
        [5, 14, 10, 2, 0],
      .equation 6 false false
        [1025]
        [14, 10, 2, 0],
      .equation 12 true false
        [1025, 14]
        [10, 2, 0],
      .equation 549 false false
        []
        [15, 10, 2, 0],
      .equation 12 false false
        [1023]
        [10, 2, 0],
      .equation 8 true false
        [1023, 10]
        [2, 0],
      .equation 548 false false
        []
        [11, 2, 0],
      .equation 8 false false
        [1021]
        [2, 0],
      .equation 4 true false
        [1021, 2]
        [0],
      .equation 547 false false
        []
        [3, 0],
      .equation 4 false false
        [435]
        [0],
      .equation 2 true false
        [435, 0]
        [],
      .prior 2506 false [],
      .prior 2997 false []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0
    ], [1017, 0], [
      .prior 3085 false [
        6, 12, 4, 14, 10, 2, 0
      ],
      .equation 17 true false
        [375, 6]
        [12, 4, 14, 10, 2, 0],
      .prior 2631 false [12, 4, 14, 10, 2, 0],
      .equation 10 true false
        [375, 12]
        [4, 14, 10, 2, 0],
      .prior 2531 false [4, 14, 10, 2, 0],
      .equation 6 true false
        [379, 4]
        [14, 10, 2, 0],
      .prior 2639 false [14, 10, 2, 0],
      .equation 12 true false
        [379, 14]
        [10, 2, 0],
      .prior 3022 false [10, 2, 0],
      .equation 8 true false
        [1019, 10]
        [2, 0],
      .prior 3019 false [2, 0],
      .equation 4 true false
        [1019, 2]
        [0],
      .prior 3017 false [0]]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2
    ], [835, 2], [
      .prior 3086 false [6, 12, 4, 14, 10, 2],
      .equation 2 true false
        [1017, 0]
        [6, 12, 4, 14, 10, 2],
      .prior 3013 false [6, 12, 4, 14, 10, 2],
      .equation 17 true false
        [1017, 6]
        [12, 4, 14, 10, 2],
      .prior 3011 true [7, 12, 4, 14, 10, 2],
      .equation 22 false false
        [1015, 6]
        [12, 12, 4, 14, 10, 2],
      .prior 3014 false [12, 4, 14, 10, 2],
      .prior 3012 false [12, 4, 14, 10, 2],
      .equation 10 true false
        [1017, 12]
        [4, 14, 10, 2],
      .prior 3010 false [4, 14, 10, 2],
      .equation 6 true false
        [1015, 4]
        [14, 10, 2],
      .prior 2981 false [14, 10, 2],
      .equation 12 true false
        [501, 14]
        [10, 2],
      .equation 288 true false
        []
        [10, 2],
      .equation 8 true false
        [503, 10]
        [2],
      .prior 2566 false [2]]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10
    ], [451, 11], [
      .prior 3087 false [0, 6, 12, 4, 14, 10],
      .equation 4 true false
        [835, 2]
        [0, 6, 12, 4, 14, 10],
      .prior 2553 false [0, 6, 12, 4, 14, 10],
      .equation 2 true false
        [835, 0]
        [6, 12, 4, 14, 10],
      .prior 2548 false [6, 12, 4, 14, 10],
      .equation 17 true false
        [835, 6]
        [12, 4, 14, 10],
      .prior 2473 false [12, 4, 14, 10],
      .equation 10 true false
        [585, 12]
        [4, 14, 10],
      .prior 2248 false [4, 14, 10],
      .equation 6 true false
        [585, 4]
        [14, 10],
      .prior 2436 false [14, 10],
      .equation 12 true false
        [585, 14]
        [10],
      .equation 330 true false
        []
        [10],
      .prior 2427 false [10],
      .equation 8 true false
        [451, 10]
        []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 8, 6, 12, 4
    ], [1013], [
      .prior 3088 false [2, 0, 8, 6, 12, 4],
      .prior 2353 false [2, 0, 8, 6, 12, 4],
      .equation 4 true false
        [737, 2]
        [0, 8, 6, 12, 4],
      .prior 2442 false [0, 8, 6, 12, 4],
      .equation 2 true false
        [737, 0]
        [8, 6, 12, 4],
      .prior 2382 false [8, 6, 12, 4],
      .equation 1 true false
        [737, 8]
        [6, 12, 4],
      .prior 2401 false [6, 12, 4],
      .equation 17 true false
        [155, 6]
        [12, 4],
      .prior 1943 false [12, 4],
      .equation 10 true false
        [155, 12]
        [4],
      .prior 2980 false [4],
      .equation 6 true false
        [1013, 4]
        [],
      .prior 2972 false []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 8, 6, 12, 4, 14, 10,
      2, 0, 6, 12
    ], [75], [
      .prior 3089 false [14, 10, 2, 0, 6, 12],
      .equation 12 true false
        [1013, 14]
        [10, 2, 0, 6, 12],
      .prior 2962 false [10, 2, 0, 6, 12],
      .equation 8 true false
        [161, 10]
        [2, 0, 6, 12],
      .prior 2557 false [2, 0, 6, 12],
      .equation 4 true false
        [161, 2]
        [0, 6, 12],
      .prior 1883 false [0, 6, 12],
      .equation 2 true false
        [161, 0]
        [6, 12],
      .prior 1880 false [6, 12],
      .equation 17 true false
        [69, 6]
        [12],
      .prior 1866 false [12],
      .equation 10 true false
        [69, 12]
        [],
      .prior 1869 false []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 8, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12
    ], [1011, 12], [
      .prior 3090 false [
        4, 14, 10, 2, 0, 6, 12
      ],
      .equation 6 true false
        [75, 4]
        [14, 10, 2, 0, 6, 12],
      .prior 1891 false [14, 10, 2, 0, 6, 12],
      .equation 12 true false
        [75, 14]
        [10, 2, 0, 6, 12],
      .prior 1876 false [10, 2, 0, 6, 12],
      .equation 8 true false
        [75, 10]
        [2, 0, 6, 12],
      .prior 1873 false [2, 0, 6, 12],
      .equation 4 true false
        [75, 2]
        [0, 6, 12],
      .prior 2953 false [0, 6, 12],
      .equation 2 true false
        [1011, 0]
        [6, 12],
      .prior 2950 false [6, 12],
      .equation 17 true false
        [1011, 6]
        [12],
      .prior 2956 false [12]]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 8, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6
    ], [57, 7], [
      .prior 3091 false [4, 14, 10, 2, 0, 6],
      .equation 10 true false
        [1011, 12]
        [4, 14, 10, 2, 0, 6],
      .prior 2945 false [4, 14, 10, 2, 0, 6],
      .equation 6 true false
        [167, 4]
        [14, 10, 2, 0, 6],
      .prior 2942 false [14, 10, 2, 0, 6],
      .equation 12 true false
        [1009, 14]
        [10, 2, 0, 6],
      .prior 2944 false [10, 2, 0, 6],
      .equation 8 true false
        [1009, 10]
        [2, 0, 6],
      .prior 2930 false [2, 0, 6],
      .equation 4 true false
        [173, 2]
        [0, 6],
      .prior 488 false [0, 6],
      .equation 2 true false
        [173, 0]
        [6],
      .prior 1820 false [6],
      .equation 17 true false
        [57, 6]
        []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 8, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0
    ], [45], [
      .prior 3092 false [12, 4, 14, 10, 2, 0],
      .prior 1806 false [12, 4, 14, 10, 2, 0],
      .equation 10 true false
        [179, 12]
        [4, 14, 10, 2, 0],
      .prior 463 false [4, 14, 10, 2, 0],
      .equation 6 true false
        [179, 4]
        [14, 10, 2, 0],
      .prior 1803 false [14, 10, 2, 0],
      .equation 12 true false
        [179, 14]
        [10, 2, 0],
      .prior 1796 false [10, 2, 0],
      .equation 8 true false
        [1007, 10]
        [2, 0],
      .prior 1791 false [2, 0],
      .equation 4 true false
        [1007, 2]
        [0],
      .prior 1778 false [0],
      .equation 2 true false
        [185, 0]
        [],
      .prior 384 false []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 8, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2
    ], [1005], [
      .prior 3093 false [6, 12, 4, 14, 10, 2],
      .equation 17 true false
        [45, 6]
        [12, 4, 14, 10, 2],
      .prior 389 false [12, 4, 14, 10, 2],
      .equation 10 true false
        [49, 12]
        [4, 14, 10, 2],
      .prior 417 false [4, 14, 10, 2],
      .equation 6 true false
        [49, 4]
        [14, 10, 2],
      .prior 392 false [14, 10, 2],
      .equation 12 true false
        [49, 14]
        [10, 2],
      .prior 406 false [10, 2],
      .equation 8 true false
        [49, 10]
        [2],
      .prior 1775 false [2],
      .equation 4 true false
        [1005, 2]
        [],
      .prior 1770 false []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 8, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2
    ], [321, 2], [
      .prior 3094 false [
        0, 6, 12, 4, 14, 10, 2
      ],
      .equation 2 true false
        [1005, 0]
        [6, 12, 4, 14, 10, 2],
      .prior 1768 false [6, 12, 4, 14, 10, 2],
      .equation 17 true false
        [1005, 6]
        [12, 4, 14, 10, 2],
      .prior 1764 false [12, 4, 14, 10, 2],
      .equation 10 true false
        [1003, 12]
        [4, 14, 10, 2],
      .prior 1680 false [4, 14, 10, 2],
      .equation 6 true false
        [1001, 4]
        [14, 10, 2],
      .prior 1667 false [14, 10, 2],
      .equation 12 true false
        [321, 14]
        [10, 2],
      .prior 853 false [10, 2],
      .equation 8 true false
        [321, 10]
        [2],
      .prior 848 false [2]]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 8, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10
    ], [213, 11], [
      .prior 3095 false [0, 6, 12, 4, 14, 10],
      .equation 4 true false
        [321, 2]
        [0, 6, 12, 4, 14, 10],
      .prior 838 false [0, 6, 12, 4, 14, 10],
      .equation 2 true false
        [203, 0]
        [6, 12, 4, 14, 10],
      .prior 295 false [6, 12, 4, 14, 10],
      .equation 17 true false
        [33, 6]
        [12, 4, 14, 10],
      .prior 109 false [12, 4, 14, 10],
      .equation 10 true false
        [33, 12]
        [4, 14, 10],
      .equation 46 true false
        []
        [4, 14, 10],
      .equation 6 true false
        [35, 4]
        [14, 10],
      .prior 119 false [14, 10],
      .equation 12 true false
        [35, 14]
        [10],
      .prior 534 false [10],
      .equation 8 true false
        [213, 10]
        []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 8, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14
    ], [33], [
      .prior 3096 false [2, 0, 6, 12, 4, 14],
      .prior 531 false [2, 0, 6, 12, 4, 14],
      .equation 4 true false
        [213, 2]
        [0, 6, 12, 4, 14],
      .prior 524 false [0, 6, 12, 4, 14],
      .equation 2 true false
        [213, 0]
        [6, 12, 4, 14],
      .prior 522 false [6, 12, 4, 14],
      .equation 17 true false
        [213, 6]
        [12, 4, 14],
      .prior 528 false [12, 4, 14],
      .equation 10 true false
        [213, 12]
        [4, 14],
      .prior 518 false [4, 14],
      .equation 6 true false
        [31, 4]
        [14],
      .prior 91 false [14],
      .equation 12 true false
        [31, 14]
        [],
      .equation 45 true false
        []
        []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 8, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4
    ], [211], [
      .prior 3097 false [10, 2, 0, 6, 12, 4],
      .equation 8 true false
        [33, 10]
        [2, 0, 6, 12, 4],
      .prior 271 false [2, 0, 6, 12, 4],
      .equation 4 true false
        [211, 2]
        [0, 6, 12, 4],
      .prior 279 false [0, 6, 12, 4],
      .equation 2 true false
        [211, 0]
        [6, 12, 4],
      .prior 277 false [6, 12, 4],
      .equation 17 true false
        [211, 6]
        [12, 4],
      .prior 283 false [12, 4],
      .equation 10 true false
        [211, 12]
        [4],
      .prior 287 false [4],
      .equation 6 true false
        [211, 4]
        [],
      .prior 281 false []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 8, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8, 6,
      12
    ], [31, 12], [
      .prior 3098 false [
        14, 10, 2, 0, 8, 6, 12
      ],
      .equation 12 true false
        [211, 14]
        [10, 2, 0, 8, 6, 12],
      .prior 266 false [10, 2, 0, 8, 6, 12],
      .equation 8 true false
        [29, 10]
        [2, 0, 8, 6, 12],
      .equation 42 true false
        []
        [2, 0, 8, 6, 12],
      .equation 4 true false
        [31, 2]
        [0, 8, 6, 12],
      .prior 89 false [0, 8, 6, 12],
      .equation 2 true false
        [31, 0]
        [8, 6, 12],
      .prior 87 false [8, 6, 12],
      .equation 1 true false
        [31, 8]
        [6, 12],
      .prior 95 false [6, 12],
      .equation 17 true false
        [31, 6]
        [12],
      .prior 93 false [12]]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 8, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8, 6,
      12, 4, 14, 10, 2, 0, 6
    ], [37, 7], [
      .prior 3099 false [4, 14, 10, 2, 0, 6],
      .equation 10 true false
        [31, 12]
        [4, 14, 10, 2, 0, 6],
      .equation 140 true false
        []
        [4, 14, 10, 2, 0, 6],
      .equation 6 true false
        [213, 4]
        [14, 10, 2, 0, 6],
      .prior 526 false [14, 10, 2, 0, 6],
      .equation 12 true false
        [213, 14]
        [10, 2, 0, 6],
      .prior 533 false [10, 2, 0, 6],
      .equation 8 true false
        [35, 10]
        [2, 0, 6],
      .prior 312 false [2, 0, 6],
      .equation 4 true false
        [35, 2]
        [0, 6],
      .prior 117 false [0, 6],
      .equation 2 true false
        [35, 0]
        [6],
      .equation 47 true false
        []
        [6],
      .equation 17 true false
        [37, 6]
        []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 8, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0
    ], [323], [
      .prior 3100 false [12, 4, 14, 10, 2, 0],
      .prior 132 false [12, 4, 14, 10, 2, 0],
      .equation 10 true false
        [37, 12]
        [4, 14, 10, 2, 0],
      .prior 307 false [4, 14, 10, 2, 0],
      .equation 6 true false
        [203, 4]
        [14, 10, 2, 0],
      .prior 300 false [14, 10, 2, 0],
      .equation 12 true false
        [203, 14]
        [10, 2, 0],
      .prior 299 false [10, 2, 0],
      .equation 8 true false
        [203, 10]
        [2, 0],
      .prior 315 false [2, 0],
      .equation 4 true false
        [203, 2]
        [0],
      .prior 836 false [0],
      .prior 840 false [0],
      .equation 2 true false
        [321, 0]
        [],
      .equation 197 true false
        []
        []]⟩,
    ⟨[
      1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 8, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2
    ], [45], [
      .prior 3101 false [6, 12, 4, 14, 10, 2],
      .prior 840 false [6, 12, 4, 14, 10, 2],
      .equation 17 true false
        [321, 6]
        [12, 4, 14, 10, 2],
      .prior 846 false [12, 4, 14, 10, 2],
      .equation 10 true false
        [321, 12]
        [4, 14, 10, 2],
      .prior 851 false [4, 14, 10, 2],
      .equation 6 true false
        [39, 4]
        [14, 10, 2],
      .prior 1692 false [14, 10, 2],
      .equation 12 true false
        [1003, 14]
        [10, 2],
      .prior 1697 false [10, 2],
      .equation 8 true false
        [1003, 10]
        [2],
      .prior 1701 false [2],
      .equation 4 true false
        [45, 2]
        [],
      .prior 369 false []]⟩,
    ⟨[1179, 15], [51], [
      .prior 3072 true [15],
      .equation 135 false false
        [
          1177, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
          4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
          6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
          2, 0
        ]
        [
          8, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
          10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
          4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
          6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
          2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
          14, 10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0,
          6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
          2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
          14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
          12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
          0, 6, 12, 4, 14, 10, 2, 0, 8, 6, 12, 4,
          14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
          12, 4, 14, 10, 2, 0, 6, 12, 4
        ],
      .prior 3102 false [0, 6, 12, 4],
      .equation 2 true false
        [45, 0]
        [6, 12, 4],
      .prior 383 false [6, 12, 4],
      .equation 17 true false
        [185, 6]
        [12, 4],
      .prior 413 false [12, 4],
      .equation 10 true false
        [51, 12]
        [4],
      .prior 434 false [4],
      .equation 6 true false
        [51, 4]
        [],
      .prior 421 false [],
      .prior 412 false []]⟩,
    ⟨[51, 15], [1179], [
      .prior 3103 true [15],
      .equation 12 false false
        [1179]
        []]⟩,
    ⟨[1177, 15], [1177, 15], [
]⟩,
    ⟨[1177, 15], [51], [
      .prior 3105 false [],
      .equation 8 true false
        [1177]
        [15],
      .equation 626 true false
        []
        [11, 15],
      .equation 136 false false
        [1179]
        [14, 10],
      .equation 12 true false
        [1179, 14]
        [10],
      .prior 3103 false [10],
      .equation 8 true false
        [51, 10]
        [],
      .prior 425 false [],
      .prior 412 false []]⟩,
    ⟨[51, 15], [1179], [
      .prior 3104 false []]⟩,
    ⟨[1177, 15], [51], [
      .prior 3105 false [],
      .prior 3106 false []]⟩,
    ⟨[1179], [1177], [
      .prior 3107 true [],
      .prior 3106 true [15],
      .equation 12 false false
        [1177]
        []]⟩,
    ⟨[1177, 1], [1177, 1], [
]⟩,
    ⟨[1177], [1177], [
]⟩,
    ⟨[1177, 1], [1177], [
      .prior 3110 false [],
      .prior 3109 true [1],
      .prior 3104 true [1],
      .equation 54 false false
        []
        [15, 1],
      .prior 406 true [1, 15, 1],
      .prior 156 true [15, 1, 15, 1],
      .prior 3108 true [1, 15, 1, 15, 1],
      .equation 137 false false
        [1177, 0]
        [1],
      .prior 3111 false []]⟩,
    ⟨[57, 3], [57, 3], [
]⟩,
    ⟨[57, 3], [1177], [
      .prior 3113 false [],
      .prior 453 true [3],
      .equation 55 false false
        []
        [15, 3],
      .prior 3108 true [3, 15, 3],
      .equation 36 false false
        [1177, 2]
        [3],
      .prior 3111 false []]⟩,
    ⟨[1177, 3], [1175], [
      .prior 3071 false []]⟩,
    ⟨[1175], [57], [
      .prior 3115 true [],
      .prior 3114 true [3],
      .equation 4 false false
        [57]
        []]⟩,
    ⟨[1169, 5], [177, 5], [
      .prior 3068 true [5],
      .prior 3069 true [13, 5],
      .prior 3070 true [7, 13, 5],
      .prior 3116 false [1, 7, 13, 5],
      .prior 1821 false [7, 13, 5],
      .prior 501 false [13, 5],
      .prior 485 false [5]]⟩,
    ⟨[177, 11], [1163], [
      .prior 1800 true [11],
      .prior 1814 true [15, 11],
      .prior 3117 true [15, 11],
      .prior 3067 false [15, 11],
      .prior 3066 false [11],
      .prior 3065 false []]⟩,
    ⟨[1177, 5], [1177, 5], [
]⟩,
    ⟨[1177, 5], [1177], [
      .prior 3119 false [],
      .prior 3109 true [5],
      .prior 3104 true [5],
      .prior 421 true [15, 5],
      .prior 3108 true [5, 15, 5],
      .equation 30 false false
        [1177, 4]
        [5],
      .prior 3111 false []]⟩,
    ⟨[181, 7], [181, 7], [
]⟩,
    ⟨[181, 7], [1177], [
      .prior 3121 false [],
      .prior 430 true [7],
      .prior 221 true [7],
      .prior 414 true [15, 7],
      .prior 3108 true [7, 15, 7],
      .equation 23 false false
        [1177, 6]
        [7],
      .prior 3111 false []]⟩,
    ⟨[1177, 7], [181], [
      .prior 3122 true [7],
      .equation 17 false false
        [181]
        []]⟩,
    ⟨[1177, 13], [1177, 13], [
]⟩,
    ⟨[1177, 13], [1177], [
      .prior 3124 false [],
      .prior 3109 true [13],
      .prior 3104 true [13],
      .prior 434 true [15, 13],
      .prior 3108 true [13, 15, 13],
      .equation 138 false false
        [1177, 12]
        [13],
      .prior 3111 false []]⟩,
    ⟨[173, 7], [177], [
      .prior 500 false [],
      .prior 501 false []]⟩,
    ⟨[1163, 7], [1009], [
      .prior 3118 true [7],
      .prior 3126 true [11, 7],
      .equation 21 false false
        [173]
        [10],
      .equation 8 true false
        [173, 10]
        [],
      .equation 541 true false
        []
        [],
      .prior 2934 false []]⟩,
    ⟨[1009, 7], [1163], [
      .prior 3127 true [7],
      .equation 17 false false
        [1163]
        []]⟩,
    ⟨[177, 1], [179], [
      .equation 118 true false
        []
        []]⟩,
    ⟨[177, 10], [1163], [
      .equation 8 true false
        [177, 10]
        [],
      .prior 3118 false []]⟩,
    ⟨[1161, 11], [177], [
      .prior 3064 true [11],
      .prior 3118 true [3, 11],
      .prior 467 true [11, 3, 11],
      .equation 34 false false
        [177]
        [],
      .prior 444 false []]⟩,
    ⟨[177, 11], [1163], [
      .prior 3118 false []]⟩,
    ⟨[1163], [1161], [
      .prior 3132 true [],
      .prior 3131 true [11],
      .equation 8 false false
        [1161]
        []]⟩,
    ⟨[1163], [1161], [
      .prior 3133 false []]⟩,
    ⟨[1161], [1159], [
      .prior 3134 true [],
      .prior 3130 true [],
      .equation 43 true false
        [177]
        [10],
      .prior 3129 false [11, 1, 11, 1],
      .prior 460 false [1, 11, 1],
      .prior 218 false [11, 1],
      .prior 3118 false [1],
      .prior 3134 false [1],
      .prior 3063 false []]⟩,
    ⟨[1163], [1159], [
      .prior 3134 false [],
      .prior 3135 false []]⟩,
    ⟨[1159, 3], [1159], [
      .prior 3135 true [3],
      .equation 618 true false
        []
        [],
      .prior 3136 false []]⟩,
    ⟨[1159, 11], [177], [
      .prior 3135 true [11],
      .prior 3131 false []]⟩,
    ⟨[1161], [1159], [
      .prior 3135 false []]⟩,
    ⟨[1157], [1009], [
      .prior 3062 true [],
      .prior 3139 true [7],
      .prior 3133 true [7],
      .prior 3127 false []]⟩,
    ⟨[1009, 13], [1155], [
      .prior 3140 true [13],
      .prior 3061 false []]⟩,
    ⟨[177, 9], [177], [
      .prior 482 false [],
      .prior 482 false [],
      .prior 218 true [9],
      .prior 480 true [1, 9],
      .equation 3 false false
        [179, 0]
        [],
      .prior 481 false [],
      .prior 444 false []]⟩,
    ⟨[177, 10], [1159], [
      .prior 3130 false [],
      .prior 3136 false []]⟩,
    ⟨[1159, 9], [1159, 9], [
]⟩,
    ⟨[1159], [1159], [
]⟩,
    ⟨[1159, 9], [1159], [
      .prior 3144 false [],
      .prior 3136 true [9],
      .prior 3118 true [9],
      .prior 3142 true [11, 9],
      .equation 9 false false
        [177]
        [10],
      .prior 3143 false [],
      .prior 3145 false []]⟩,
    ⟨[1159, 15], [1159, 15], [
]⟩,
    ⟨[1159, 15], [1159], [
      .prior 3147 false [],
      .prior 3136 true [15],
      .prior 3118 true [15],
      .prior 1808 true [11, 15],
      .equation 136 false false
        [177, 10]
        [],
      .prior 3143 false [],
      .prior 3145 false []]⟩,
    ⟨[1159, 5], [1159, 5], [
]⟩,
    ⟨[1159, 5], [1159], [
      .prior 3149 false [],
      .prior 3136 true [5],
      .prior 3118 true [5],
      .prior 1825 true [11, 5],
      .equation 28 false false
        [177]
        [10],
      .prior 3143 false [],
      .prior 3145 false []]⟩,
    ⟨[1009, 11], [173], [
      .prior 2930 false []]⟩,
    ⟨[1009, 12], [1155], [
      .equation 10 true false
        [1009, 12]
        [],
      .prior 3141 false []]⟩,
    ⟨[1155, 11], [1155, 11], [
]⟩,
    ⟨[1155], [1155], [
]⟩,
    ⟨[1155, 11], [1155], [
      .prior 3153 false [],
      .prior 3141 true [11],
      .equation 541 false false
        []
        [13, 11],
      .prior 503 true [11, 13, 11],
      .equation 116 false false
        []
        [11, 13, 11],
      .prior 3151 true [13, 11, 13, 11],
      .equation 139 false false
        [1009]
        [12],
      .prior 3152 false [],
      .prior 3154 false []]⟩,
    ⟨[1009, 1], [1009], [
      .prior 2933 false [],
      .prior 2935 false []]⟩,
    ⟨[1155, 1], [1155, 1], [
]⟩,
    ⟨[1155, 1], [1155], [
      .prior 3157 false [],
      .prior 3141 true [1],
      .prior 3156 true [13, 1],
      .equation 40 false false
        [1009]
        [12],
      .prior 3152 false [],
      .prior 3154 false []]⟩,
    ⟨[1009, 3], [1009], [
      .prior 2937 false [],
      .prior 2938 false []]⟩,
    ⟨[1155, 3], [1155, 3], [
]⟩,
    ⟨[1009, 5], [167], [
      .prior 2940 false [],
      .prior 2941 false []]⟩,
    ⟨[1011, 5], [1011, 5], [
]⟩,
    ⟨[1011, 5], [1155], [
      .prior 3162 false [],
      .equation 542 false false
        []
        [5],
      .prior 3161 true [13, 5],
      .equation 29 false false
        [1009]
        [12],
      .prior 3152 false [],
      .prior 3154 false []]⟩,
    ⟨[1155, 5], [1153], [
      .prior 3060 false []]⟩,
    ⟨[1153], [1011], [
      .prior 3164 true [],
      .prior 3163 true [5],
      .equation 6 false false
        [1011]
        []]⟩,
    ⟨[1147, 1], [75, 1], [
      .prior 3057 true [1],
      .prior 3058 true [3, 1],
      .prior 3059 true [11, 3, 1],
      .prior 3165 false [15, 11, 3, 1],
      .prior 2961 false [11, 3, 1],
      .prior 2959 false [3, 1],
      .prior 2952 false [1]]⟩,
    ⟨[1141, 5], [161], [
      .prior 3054 true [5],
      .prior 3055 true [13, 5],
      .prior 3056 true [7, 13, 5],
      .prior 3166 false [7, 13, 5],
      .prior 1886 false [7, 13, 5],
      .prior 1898 false [7, 13, 5],
      .prior 1913 false [13, 5],
      .prior 1897 false [5],
      .prior 1884 false []]⟩,
    ⟨[1135, 3], [1013], [
      .prior 3051 true [3],
      .prior 3052 true [11, 3],
      .prior 3053 true [15, 11, 3],
      .prior 3167 false [15, 11, 3],
      .equation 543 true false
        []
        [11, 3],
      .prior 2976 false [3],
      .prior 2969 false []]⟩,
    ⟨[155], [1129, 13], [
      .prior 2979 true [],
      .prior 2974 true [13],
      .prior 2966 true [7, 13],
      .prior 3168 true [1, 7, 13],
      .prior 3050 false [1, 7, 13],
      .prior 3049 false [7, 13],
      .prior 3048 false [13]]⟩,
    ⟨[83], [1121], [
      .prior 1900 true [],
      .prior 1926 true [11],
      .equation 107 false false
        []
        [11],
      .prior 1931 true [15, 11],
      .prior 3169 false [5, 15, 11],
      .prior 3047 false [5, 15, 11],
      .prior 3046 false [15, 11],
      .prior 3045 false [11],
      .prior 3044 false []]⟩,
    ⟨[83], [1115], [
      .prior 1935 true [],
      .prior 1904 true [7],
      .prior 1923 true [1, 7],
      .prior 3170 false [3, 1, 7],
      .prior 3043 false [1, 7],
      .prior 3042 false [7],
      .prior 3041 false []]⟩,
    ⟨[1109], [85], [
      .prior 3038 true [],
      .prior 3039 true [15],
      .prior 3040 true [5, 15],
      .prior 3171 true [13, 5, 15],
      .prior 2396 false [5, 15],
      .prior 1929 false [15],
      .equation 71 true false
        []
        []]⟩,
    ⟨[1103], [155], [
      .prior 3035 true [],
      .prior 3036 true [1],
      .prior 3037 true [3, 1],
      .prior 3172 false [11, 3, 1],
      .prior 1937 false [3, 1],
      .prior 1925 false [1],
      .prior 1918 false []]⟩,
    ⟨[501, 13], [1097], [
      .prior 2445 true [13],
      .prior 2400 true [7, 13],
      .prior 3173 true [9, 7, 13],
      .prior 3034 false [7, 13],
      .prior 3033 false [13],
      .prior 3032 false []]⟩,
    ⟨[1009, 15], [1009], [
      .prior 2943 false [],
      .prior 2944 false []]⟩,
    ⟨[1155, 15], [1155, 15], [
]⟩,
    ⟨[1155, 15], [1155], [
      .prior 3176 false [],
      .prior 3141 true [15],
      .prior 3175 true [13, 15],
      .equation 138 false false
        [1009, 12]
        [],
      .prior 3152 false [],
      .prior 3154 false []]⟩,
    ⟨[501, 12], [1097], [
      .equation 10 true false
        [501, 12]
        [],
      .prior 3174 false []]⟩,
    ⟨[1097], [1097], [
]⟩,
    ⟨[745, 15], [745, 15], [
]⟩,
    ⟨[745, 15], [1097], [
      .prior 3180 false [],
      .prior 2662 true [15],
      .equation 288 false false
        []
        [13, 15],
      .equation 138 false false
        [501, 12]
        [],
      .prior 3178 false [],
      .prior 3179 false []]⟩,
    ⟨[1095], [1017], [
      .prior 3031 true [],
      .prior 3179 true [5],
      .prior 3178 true [5],
      .equation 29 true false
        [501]
        [12, 5],
      .prior 2982 false [13, 5, 5],
      .equation 545 true false
        []
        [5, 5],
      .equation 6 false false
        [1017]
        []]⟩,
    ⟨[1089, 1], [379, 1], [
      .prior 3028 true [1],
      .prior 3029 true [3, 1],
      .prior 3030 true [11, 3, 1],
      .prior 3182 false [15, 11, 3, 1],
      .prior 3016 false [11, 3, 1],
      .prior 2614 false [3, 1],
      .prior 3005 false [1]]⟩,
    ⟨[1083, 5], [435], [
      .prior 3025 true [5],
      .prior 3026 true [13, 5],
      .prior 3027 true [7, 13, 5],
      .prior 3183 false [7, 13, 5],
      .prior 2643 false [7, 13, 5],
      .prior 2721 false [13, 5],
      .prior 2999 false [5],
      .prior 2623 false []]⟩,
    ⟨[1081], [435], [
      .prior 3024 true [],
      .prior 3184 false []]⟩,
    ⟨[429, 13], [1079], [
      .prior 2515 true [13],
      .prior 3001 true [13],
      .equation 12 false false
        [383, 14]
        [13],
      .equation 138 true false
        [383]
        [14, 13],
      .prior 2998 false [15, 13, 13],
      .prior 2999 false [15, 13, 13],
      .prior 3185 true [15, 13, 13],
      .prior 3023 false [13, 13],
      .equation 10 false false
        [1079]
        []]⟩,
    ⟨[1181, 17], [203], [
      .equation 627 false false
        []
        [17],
      .equation 14 false false
        [203]
        []]⟩,
    ⟨[203, 17], [1181], [
      .equation 627 true false
        []
        []]⟩,
    ⟨[1181, 1], [1181, 1], [
]⟩,
    ⟨[1181, 1], [611], [
      .prior 3189 false [],
      .prior 3188 true [1],
      .equation 41 false false
        [203, 0]
        [16],
      .equation 2 true false
        [203, 0]
        [16],
      .prior 295 false [16],
      .equation 14 true false
        [33, 16]
        [],
      .prior 1153 false [],
      .prior 1142 false []]⟩,
    ⟨[611, 1], [1181], [
      .prior 3190 true [1],
      .equation 2 false false
        [1181]
        []]⟩,
    ⟨[1181, 3], [1181, 3], [
]⟩,
    ⟨[1181, 3], [319], [
      .prior 3192 false [],
      .prior 3188 true [3],
      .equation 37 false false
        [203, 2]
        [16],
      .equation 4 true false
        [203, 2]
        [16],
      .prior 836 false [16],
      .prior 840 false [16],
      .equation 14 true false
        [321, 16]
        [],
      .prior 814 false [],
      .prior 812 false []]⟩,
    ⟨[319, 3], [1181], [
      .prior 3193 true [3],
      .equation 4 false false
        [1181]
        []]⟩,
    ⟨[1181, 5], [1181, 5], [
]⟩,
    ⟨[1181], [1181], [
]⟩,
    ⟨[1181, 5], [1181], [
      .prior 3195 false [],
      .prior 3188 true [5],
      .equation 31 false false
        [203, 4]
        [16],
      .equation 6 true false
        [203, 4]
        [16],
      .prior 300 false [16],
      .equation 14 true false
        [203, 16]
        [],
      .equation 627 true false
        []
        [],
      .prior 3196 false []]⟩,
    ⟨[1181, 7], [1181, 7], [
]⟩,
    ⟨[1181, 7], [1181], [
      .prior 3198 false [],
      .prior 3188 true [7],
      .equation 24 false false
        [203, 6]
        [16],
      .equation 17 true false
        [203, 6]
        [16],
      .equation 131 true false
        []
        [16],
      .prior 298 false [16],
      .equation 14 true false
        [203, 16]
        [],
      .equation 627 true false
        []
        [],
      .prior 3196 false []]⟩]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
