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
def y422CosetData31 : Fin 128 → Y522RawCosetCertificate :=
  ![
    ⟨[1331, 5], [577], [
      .equation 702 false false
        []
        [5],
      .equation 6 false false
        [577]
        []]⟩,
    ⟨[577, 5], [1331], [
      .equation 702 true false
        []
        []]⟩,
    ⟨[1331, 1], [1331, 1], [
]⟩,
    ⟨[1331, 1], [441], [
      .prior 3970 false [],
      .prior 3969 true [1],
      .equation 26 false false
        [577, 0]
        [4],
      .equation 2 true false
        [577, 0]
        [4],
      .prior 2672 false [4],
      .prior 3798 false [4],
      .equation 6 true false
        [415, 4]
        [],
      .prior 3797 false [],
      .prior 2496 false []]⟩,
    ⟨[441, 1], [1331], [
      .prior 3971 true [1],
      .equation 2 false false
        [1331]
        []]⟩,
    ⟨[1331, 3], [1331, 3], [
]⟩,
    ⟨[1331], [1331], [
]⟩,
    ⟨[1331, 3], [1331], [
      .prior 3973 false [],
      .prior 3969 true [3],
      .equation 33 false false
        [577, 2]
        [4, 2, 4],
      .equation 4 true false
        [577, 2]
        [4, 2, 4],
      .prior 3958 false [4, 2, 4],
      .equation 6 true false
        [1329, 4]
        [2, 4],
      .prior 3960 false [2, 4],
      .equation 4 true false
        [1329, 2]
        [4],
      .prior 3957 false [4],
      .equation 6 true false
        [577, 4]
        [],
      .equation 702 true false
        []
        [],
      .prior 3974 false []]⟩,
    ⟨[1331, 7], [1331, 7], [
]⟩,
    ⟨[1331, 9], [1331, 9], [
]⟩,
    ⟨[1331, 11], [1331, 11], [
]⟩,
    ⟨[1331, 13], [1331, 13], [
]⟩,
    ⟨[1331, 13], [511], [
      .prior 3979 false [],
      .prior 3969 true [13],
      .equation 29 false false
        [577]
        [12, 4],
      .prior 2698 false [4],
      .prior 3887 false [4],
      .equation 6 true false
        [555, 4]
        [],
      .prior 3885 false [],
      .prior 2703 false []]⟩,
    ⟨[1331, 15], [1331, 15], [
]⟩,
    ⟨[1331, 15], [1331], [
      .prior 3981 false [],
      .prior 3969 true [15],
      .equation 30 false false
        [577]
        [14, 4],
      .equation 12 true false
        [577, 14]
        [4],
      .prior 2677 false [4],
      .equation 6 true false
        [577, 4]
        [],
      .equation 702 true false
        []
        [],
      .prior 3974 false []]⟩,
    ⟨[1333, 1], [373], [
      .equation 703 false false
        []
        [1],
      .equation 2 false false
        [373]
        []]⟩,
    ⟨[373, 1], [1333], [
      .equation 703 true false
        []
        []]⟩,
    ⟨[1333, 3], [1333, 3], [
]⟩,
    ⟨[1333], [1333], [
]⟩,
    ⟨[1333, 3], [1333], [
      .prior 3985 false [],
      .prior 3984 true [3],
      .equation 39 false false
        [373]
        [2, 0, 2, 0],
      .equation 4 true false
        [373, 2]
        [0, 2, 0],
      .prior 2992 false [0, 2, 0],
      .prior 3791 false [0, 2, 0],
      .equation 2 true false
        [419, 0]
        [2, 0],
      .prior 3792 false [2, 0],
      .equation 4 true false
        [419, 2]
        [0],
      .prior 3793 false [0],
      .equation 2 true false
        [373, 0]
        [],
      .equation 703 true false
        []
        [],
      .prior 3986 false []]⟩,
    ⟨[1333, 5], [1333, 5], [
]⟩,
    ⟨[1333, 5], [1333], [
      .prior 3988 false [],
      .prior 3984 true [5],
      .equation 26 false false
        [373]
        [4, 0],
      .prior 2528 false [0],
      .equation 2 true false
        [373, 0]
        [],
      .equation 703 true false
        []
        [],
      .prior 3986 false []]⟩,
    ⟨[1333, 7], [1333, 7], [
]⟩,
    ⟨[1333, 7], [1333], [
      .prior 3990 false [],
      .prior 3984 true [7],
      .equation 18 false false
        [373]
        [6, 0],
      .equation 17 true false
        [373, 6]
        [0],
      .prior 2543 false [0],
      .equation 2 true false
        [373, 0]
        [],
      .equation 703 true false
        []
        [],
      .prior 3986 false []]⟩,
    ⟨[1333, 9], [1333, 9], [
]⟩,
    ⟨[1333, 9], [1333], [
      .prior 3992 false [],
      .prior 3984 true [9],
      .equation 3 false false
        [373]
        [8, 0],
      .equation 1 true false
        [373, 8]
        [0],
      .prior 2545 false [0],
      .equation 2 true false
        [373, 0]
        [],
      .equation 703 true false
        []
        [],
      .prior 3986 false []]⟩,
    ⟨[1333, 11], [1333, 11], [
]⟩,
    ⟨[1333, 11], [1333], [
      .prior 3994 false [],
      .prior 3984 true [11],
      .equation 43 false false
        [373]
        [10, 0, 10, 0],
      .equation 8 true false
        [373, 10]
        [0, 10, 0],
      .prior 949 false [0, 10, 0],
      .equation 2 true false
        [371, 0]
        [10, 0],
      .prior 2534 false [10, 0],
      .equation 8 true false
        [371, 10]
        [0],
      .equation 223 true false
        []
        [0],
      .equation 2 true false
        [373, 0]
        [],
      .equation 703 true false
        []
        [],
      .prior 3986 false []]⟩,
    ⟨[1333, 15], [1333, 15], [
]⟩,
    ⟨[1333, 15], [1333], [
      .prior 3996 false [],
      .prior 3984 true [15],
      .equation 137 false false
        [373]
        [14, 0, 14, 0],
      .equation 12 true false
        [373, 14]
        [0, 14, 0],
      .equation 224 true false
        []
        [0, 14, 0],
      .equation 2 true false
        [375, 0]
        [14, 0],
      .prior 2995 false [14, 0],
      .prior 3781 false [14, 0],
      .equation 12 true false
        [375, 14]
        [0],
      .prior 950 false [0],
      .equation 2 true false
        [373, 0]
        [],
      .equation 703 true false
        []
        [],
      .prior 3986 false []]⟩,
    ⟨[1335, 13], [1333], [
      .equation 704 false false
        []
        [13],
      .equation 10 false false
        [1333]
        []]⟩,
    ⟨[1333, 13], [1335], [
      .equation 704 true false
        []
        []]⟩,
    ⟨[1335, 1], [1335, 1], [
]⟩,
    ⟨[1335, 1], [427], [
      .prior 4000 false [],
      .prior 3999 true [1],
      .equation 40 false false
        [1333, 0]
        [12],
      .equation 2 true false
        [1333, 0]
        [12],
      .prior 3983 false [12],
      .equation 10 true false
        [373, 12]
        [],
      .prior 3021 false [],
      .prior 3787 false [],
      .prior 2518 false []]⟩,
    ⟨[427, 1], [1335], [
      .prior 4001 true [1],
      .equation 2 false false
        [1335]
        []]⟩,
    ⟨[1335, 3], [1335, 3], [
]⟩,
    ⟨[1335], [1335], [
]⟩,
    ⟨[1335, 3], [1335], [
      .prior 4003 false [],
      .prior 3999 true [3],
      .equation 35 false false
        [1333, 2]
        [12],
      .equation 4 true false
        [1333, 2]
        [12],
      .prior 3987 false [12],
      .equation 10 true false
        [1333, 12]
        [],
      .equation 704 true false
        []
        [],
      .prior 4004 false []]⟩,
    ⟨[1335, 5], [1335, 5], [
]⟩,
    ⟨[1335, 5], [1335], [
      .prior 4006 false [],
      .prior 3999 true [5],
      .equation 29 false false
        [1333, 4]
        [12],
      .equation 6 true false
        [1333, 4]
        [12],
      .prior 3989 false [12],
      .equation 10 true false
        [1333, 12]
        [],
      .equation 704 true false
        []
        [],
      .prior 4004 false []]⟩,
    ⟨[1335, 7], [1335, 7], [
]⟩,
    ⟨[1335, 7], [1335], [
      .prior 4008 false [],
      .prior 3999 true [7],
      .equation 22 false false
        [1333, 6]
        [12],
      .equation 17 true false
        [1333, 6]
        [12],
      .prior 3991 false [12],
      .equation 10 true false
        [1333, 12]
        [],
      .equation 704 true false
        []
        [],
      .prior 4004 false []]⟩,
    ⟨[1335, 9], [1335, 9], [
]⟩,
    ⟨[1335, 9], [1335], [
      .prior 4010 false [],
      .prior 3999 true [9],
      .equation 11 false false
        [1333, 8]
        [12],
      .equation 1 true false
        [1333, 8]
        [12],
      .prior 3993 false [12],
      .equation 10 true false
        [1333, 12]
        [],
      .equation 704 true false
        []
        [],
      .prior 4004 false []]⟩,
    ⟨[1335, 15], [1335, 15], [
]⟩,
    ⟨[1335, 15], [1335], [
      .prior 4012 false [],
      .prior 3999 true [15],
      .equation 138 false false
        [1333]
        [14, 12],
      .equation 12 true false
        [1333, 14]
        [12],
      .prior 3997 false [12],
      .equation 10 true false
        [1333, 12]
        [],
      .equation 704 true false
        []
        [],
      .prior 4004 false []]⟩,
    ⟨[1337, 17], [181], [
      .equation 705 false false
        []
        [17],
      .equation 14 false false
        [181]
        []]⟩,
    ⟨[181, 17], [1337], [
      .equation 705 true false
        []
        []]⟩,
    ⟨[1337, 1], [1337, 1], [
]⟩,
    ⟨[1337], [1337], [
]⟩,
    ⟨[1337, 1], [1337], [
      .prior 4016 false [],
      .prior 4015 true [1],
      .equation 41 false false
        [181, 0]
        [16],
      .equation 2 true false
        [181, 0]
        [16],
      .prior 431 false [16],
      .equation 14 true false
        [181, 16]
        [],
      .equation 705 true false
        []
        [],
      .prior 4017 false []]⟩,
    ⟨[1337, 9], [1337, 9], [
]⟩,
    ⟨[1337, 9], [1337], [
      .prior 4019 false [],
      .prior 4015 true [9],
      .equation 15 false false
        [181, 8]
        [16],
      .prior 455 false [16],
      .equation 14 true false
        [181, 16]
        [],
      .equation 705 true false
        []
        [],
      .prior 4017 false []]⟩,
    ⟨[1337, 11], [1337, 11], [
]⟩,
    ⟨[1337, 11], [1337], [
      .prior 4021 false [],
      .prior 4015 true [11],
      .equation 44 false false
        [181, 10]
        [16],
      .prior 458 false [16],
      .equation 14 true false
        [181, 16]
        [],
      .equation 705 true false
        []
        [],
      .prior 4017 false []]⟩,
    ⟨[1337, 13], [1337, 13], [
]⟩,
    ⟨[1337, 13], [1337], [
      .prior 4023 false [],
      .prior 4015 true [13],
      .equation 141 false false
        [181, 12]
        [16],
      .prior 461 false [16],
      .equation 14 true false
        [181, 16]
        [],
      .equation 705 true false
        []
        [],
      .prior 4017 false []]⟩,
    ⟨[1337, 15], [1337, 15], [
]⟩,
    ⟨[1337, 15], [231], [
      .prior 4025 false [],
      .prior 4015 true [15],
      .equation 143 false false
        [181, 14]
        [16, 14, 16],
      .equation 12 true false
        [181, 14]
        [16, 14, 16],
      .prior 427 false [16, 14, 16],
      .equation 14 true false
        [185, 16]
        [14, 16],
      .prior 1716 false [14, 16],
      .equation 12 true false
        [227, 14]
        [16],
      .equation 150 true false
        []
        [16],
      .equation 14 true false
        [229, 16]
        [],
      .equation 151 true false
        []
        [],
      .prior 611 false []]⟩,
    ⟨[231, 15], [1337], [
      .prior 4026 true [15],
      .equation 12 false false
        [1337]
        []]⟩,
    ⟨[1337, 1], [1337], [
      .prior 4016 false [],
      .prior 4018 false []]⟩,
    ⟨[1337, 14], [231], [
      .equation 12 true false
        [1337, 14]
        [],
      .prior 4026 false []]⟩,
    ⟨[233, 15], [233, 15], [
]⟩,
    ⟨[233, 15], [233], [
      .prior 4030 false [],
      .equation 152 false false
        []
        [15],
      .prior 4026 true [1, 15],
      .prior 4028 true [15, 1, 15],
      .equation 137 false false
        [1337]
        [14, 0],
      .prior 4029 false [0],
      .equation 2 true false
        [231, 0]
        [],
      .equation 152 true false
        []
        [],
      .prior 617 false []]⟩,
    ⟨[233, 15], [233], [
      .prior 4030 false [],
      .prior 4031 false []]⟩,
    ⟨[235, 15], [235, 15], [
]⟩,
    ⟨[235, 15], [235], [
      .prior 4033 false [],
      .equation 153 false false
        []
        [15],
      .prior 4032 true [3, 15],
      .equation 36 false false
        [233, 2]
        [],
      .prior 1750 false [],
      .prior 622 false []]⟩,
    ⟨[233, 4], [1187], [
      .equation 6 true false
        [233, 4]
        [],
      .prior 3244 false []]⟩,
    ⟨[1187, 15], [1187, 15], [
]⟩,
    ⟨[1187, 15], [1187], [
      .prior 4036 false [],
      .prior 3244 true [15],
      .prior 4032 true [5, 15],
      .equation 30 false false
        [233, 4]
        [],
      .prior 4035 false [],
      .prior 3246 false []]⟩,
    ⟨[235, 15], [235], [
      .prior 4033 false [],
      .prior 4034 false []]⟩,
    ⟨[237, 15], [237, 15], [
]⟩,
    ⟨[237, 15], [237], [
      .prior 4039 false [],
      .equation 154 false false
        []
        [15],
      .prior 4038 true [5, 15],
      .equation 30 false false
        [235, 4]
        [],
      .prior 1754 false [],
      .prior 627 false []]⟩,
    ⟨[1187, 15], [1187], [
      .prior 4036 false [],
      .prior 4037 false []]⟩,
    ⟨[1187, 2], [1189], [
      .equation 4 true false
        [1187, 2]
        [],
      .equation 631 true false
        []
        []]⟩,
    ⟨[1189, 15], [1189, 15], [
]⟩,
    ⟨[237, 15], [237], [
      .prior 4039 false [],
      .prior 4040 false []]⟩,
    ⟨[237, 2], [1191], [
      .equation 4 true false
        [237, 2]
        [],
      .prior 3273 false []]⟩,
    ⟨[1191, 15], [1191, 15], [
]⟩,
    ⟨[1191, 15], [1191], [
      .prior 4046 false [],
      .prior 3273 true [15],
      .prior 4044 true [3, 15],
      .equation 36 false false
        [237, 2]
        [],
      .prior 4045 false [],
      .prior 3269 false []]⟩,
    ⟨[1191, 15], [1191], [
      .prior 4046 false [],
      .prior 4047 false []]⟩,
    ⟨[1193, 15], [1193, 15], [
]⟩,
    ⟨[1193, 15], [1193], [
      .prior 4049 false [],
      .equation 633 false false
        []
        [15],
      .prior 4048 true [11, 15],
      .equation 136 false false
        [1191, 10]
        [],
      .equation 8 true false
        [1191, 10]
        [],
      .equation 633 true false
        []
        [],
      .prior 3291 false []]⟩,
    ⟨[1195, 15], [1195, 15], [
]⟩,
    ⟨[1195, 15], [1195], [
      .prior 4051 false [],
      .equation 634 false false
        []
        [15],
      .prior 4050 true [13, 15],
      .prior 4049 true [13, 15],
      .equation 138 false false
        [1193, 12]
        [],
      .equation 10 true false
        [1193, 12]
        [],
      .equation 634 true false
        []
        [],
      .prior 3295 false []]⟩,
    ⟨[1195, 15], [1195], [
      .prior 4051 false [],
      .prior 4052 false []]⟩,
    ⟨[1199, 1], [1199, 1], [
]⟩,
    ⟨[1199, 1], [1199], [
      .prior 4054 false [],
      .equation 636 false false
        []
        [1],
      .equation 635 false false
        []
        [15, 1],
      .prior 4053 true [1, 15, 1],
      .equation 137 false false
        [1195, 0]
        [14],
      .equation 2 true false
        [1195, 0]
        [14],
      .equation 635 true false
        []
        [14],
      .equation 12 true false
        [1197, 14]
        [],
      .equation 636 true false
        []
        [],
      .prior 3307 false []]⟩,
    ⟨[1199, 1], [1199], [
      .prior 4054 false [],
      .prior 4055 false []]⟩,
    ⟨[1203], [1201], [
      .equation 14 true false
        [1203]
        [],
      .equation 638 false false
        []
        [17, 17],
      .equation 637 false false
        []
        [1, 17, 17],
      .prior 4056 true [17, 1, 17, 17],
      .equation 41 false false
        [1199]
        [17],
      .prior 3307 false [17],
      .prior 3310 false []]⟩,
    ⟨[1339, 3], [1337], [
      .equation 706 false false
        []
        [3],
      .equation 4 false false
        [1337]
        []]⟩,
    ⟨[1337, 3], [1339], [
      .equation 706 true false
        []
        []]⟩,
    ⟨[1337, 8], [1337], [
      .equation 1 true false
        [1337, 8]
        [],
      .prior 4020 false []]⟩,
    ⟨[1339, 9], [1339, 9], [
]⟩,
    ⟨[1339], [1339], [
]⟩,
    ⟨[1337, 10], [1337], [
      .equation 8 true false
        [1337, 10]
        [],
      .prior 4022 false []]⟩,
    ⟨[1339, 11], [1339, 11], [
]⟩,
    ⟨[1339, 11], [1339], [
      .prior 4064 false [],
      .prior 4059 true [11],
      .equation 34 false false
        [1337]
        [10, 2],
      .prior 4063 false [2],
      .equation 4 true false
        [1337, 2]
        [],
      .equation 706 true false
        []
        [],
      .prior 4062 false []]⟩,
    ⟨[1337, 12], [1337], [
      .equation 10 true false
        [1337, 12]
        [],
      .prior 4024 false []]⟩,
    ⟨[1339, 13], [1339, 13], [
]⟩,
    ⟨[1339, 13], [1339], [
      .prior 4067 false [],
      .prior 4059 true [13],
      .equation 35 false false
        [1337]
        [12, 2],
      .prior 4066 false [2],
      .equation 4 true false
        [1337, 2]
        [],
      .equation 706 true false
        []
        [],
      .prior 4062 false []]⟩,
    ⟨[1337, 16], [181], [
      .equation 14 true false
        [1337, 16]
        [],
      .prior 4014 false []]⟩,
    ⟨[1339, 17], [1339, 17], [
]⟩,
    ⟨[1339, 17], [179], [
      .prior 4070 false [],
      .prior 4059 true [17],
      .equation 37 false false
        [1337]
        [16, 2],
      .prior 4069 false [2],
      .equation 4 true false
        [181, 2]
        [],
      .prior 219 false [],
      .prior 457 false []]⟩,
    ⟨[179, 17], [1339], [
      .prior 4071 true [17],
      .equation 14 false false
        [1339]
        []]⟩,
    ⟨[1339, 17], [179], [
      .prior 4070 false [],
      .prior 4071 false []]⟩,
    ⟨[1289, 1], [1289, 1], [
]⟩,
    ⟨[1289, 1], [1339], [
      .prior 4074 false [],
      .prior 3526 true [1],
      .prior 218 true [17, 1],
      .prior 4073 true [1, 17, 1],
      .equation 41 false false
        [1339, 0]
        [1],
      .prior 4062 false []]⟩,
    ⟨[1339, 1], [1289], [
      .prior 4075 true [1],
      .equation 2 false false
        [1289]
        []]⟩,
    ⟨[1339, 5], [1339, 5], [
]⟩,
    ⟨[1339, 5], [1339], [
      .prior 4077 false [],
      .prior 4072 true [5],
      .prior 1803 true [17, 5],
      .prior 4073 true [5, 17, 5],
      .equation 31 false false
        [1339, 4]
        [5],
      .prior 4062 false []]⟩,
    ⟨[1341, 11], [1289], [
      .equation 707 false false
        []
        [11],
      .equation 8 false false
        [1289]
        []]⟩,
    ⟨[1289, 11], [1341], [
      .equation 707 true false
        []
        []]⟩,
    ⟨[1341, 1], [1341, 1], [
]⟩,
    ⟨[1341], [1341], [
]⟩,
    ⟨[1341, 1], [1341], [
      .prior 4081 false [],
      .prior 4080 true [1],
      .equation 43 false false
        [1289, 0]
        [10, 0, 10],
      .equation 2 true false
        [1289, 0]
        [10, 0, 10],
      .prior 4075 false [10, 0, 10],
      .equation 8 true false
        [1339, 10]
        [0, 10],
      .prior 4065 false [0, 10],
      .equation 2 true false
        [1339, 0]
        [10],
      .prior 4076 false [10],
      .equation 8 true false
        [1289, 10]
        [],
      .equation 707 true false
        []
        [],
      .prior 4082 false []]⟩,
    ⟨[1341, 3], [1341, 3], [
]⟩,
    ⟨[1341, 3], [1341], [
      .prior 4084 false [],
      .prior 4080 true [3],
      .equation 34 false false
        [1289, 2]
        [10],
      .equation 4 true false
        [1289, 2]
        [10],
      .prior 3530 false [10],
      .equation 8 true false
        [1289, 10]
        [],
      .equation 707 true false
        []
        [],
      .prior 4082 false []]⟩,
    ⟨[1341, 5], [1341, 5], [
]⟩,
    ⟨[1341, 5], [1341], [
      .prior 4086 false [],
      .prior 4080 true [5],
      .equation 28 false false
        [1289, 4]
        [10],
      .equation 6 true false
        [1289, 4]
        [10],
      .prior 3536 false [10],
      .equation 8 true false
        [1289, 10]
        [],
      .equation 707 true false
        []
        [],
      .prior 4082 false []]⟩,
    ⟨[1341, 9], [1341, 9], [
]⟩,
    ⟨[1341, 9], [1341], [
      .prior 4088 false [],
      .prior 4080 true [9],
      .equation 9 false false
        [1289, 8]
        [10],
      .prior 3439 false [10],
      .equation 8 true false
        [1289, 10]
        [],
      .equation 707 true false
        []
        [],
      .prior 4082 false []]⟩,
    ⟨[1341, 17], [1341, 17], [
]⟩,
    ⟨[1341, 17], [1159], [
      .prior 4090 false [],
      .prior 4080 true [17],
      .equation 44 false false
        [1289]
        [16, 10],
      .equation 14 true false
        [1289, 16]
        [10],
      .equation 682 true false
        []
        [10],
      .prior 3527 false [10],
      .equation 8 true false
        [177, 10]
        [],
      .prior 3118 false [],
      .prior 3136 false [],
      .prior 3145 false []]⟩,
    ⟨[1159, 17], [1341], [
      .prior 4091 true [17],
      .equation 14 false false
        [1341]
        []]⟩,
    ⟨[1343, 13], [1341], [
      .equation 708 false false
        []
        [13],
      .equation 10 false false
        [1341]
        []]⟩,
    ⟨[1341, 13], [1343], [
      .equation 708 true false
        []
        []]⟩,
    ⟨[1343, 1], [1343, 1], [
]⟩]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
