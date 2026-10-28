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
def y422CosetData32 : Fin 128 → Y522RawCosetCertificate :=
  ![
    ⟨[1343], [1343], [
]⟩,
    ⟨[1343, 1], [1343], [
      .prior 4095 false [],
      .prior 4094 true [1],
      .equation 40 false false
        [1341, 0]
        [12],
      .equation 2 true false
        [1341, 0]
        [12],
      .prior 4083 false [12],
      .equation 10 true false
        [1341, 12]
        [],
      .equation 708 true false
        []
        [],
      .prior 4096 false []]⟩,
    ⟨[1341, 2], [1341], [
      .equation 4 true false
        [1341, 2]
        [],
      .prior 4085 false []]⟩,
    ⟨[1343, 3], [1343, 3], [
]⟩,
    ⟨[1343, 3], [1343], [
      .prior 4099 false [],
      .prior 4094 true [3],
      .equation 35 false false
        [1341, 2]
        [12],
      .prior 4098 false [12],
      .equation 10 true false
        [1341, 12]
        [],
      .equation 708 true false
        []
        [],
      .prior 4096 false []]⟩,
    ⟨[1341, 4], [1341], [
      .equation 6 true false
        [1341, 4]
        [],
      .prior 4087 false []]⟩,
    ⟨[1343, 5], [1343, 5], [
]⟩,
    ⟨[1343, 5], [1343], [
      .prior 4102 false [],
      .prior 4094 true [5],
      .equation 29 false false
        [1341, 4]
        [12],
      .prior 4101 false [12],
      .equation 10 true false
        [1341, 12]
        [],
      .equation 708 true false
        []
        [],
      .prior 4096 false []]⟩,
    ⟨[1341, 8], [1341], [
      .equation 1 true false
        [1341, 8]
        [],
      .prior 4089 false []]⟩,
    ⟨[1343, 9], [1343, 9], [
]⟩,
    ⟨[1343, 9], [1343], [
      .prior 4105 false [],
      .prior 4094 true [9],
      .equation 11 false false
        [1341, 8]
        [12],
      .prior 4104 false [12],
      .equation 10 true false
        [1341, 12]
        [],
      .equation 708 true false
        []
        [],
      .prior 4096 false []]⟩,
    ⟨[1341, 10], [1289], [
      .equation 8 true false
        [1341, 10]
        [],
      .prior 4079 false []]⟩,
    ⟨[1343, 11], [1343, 11], [
]⟩,
    ⟨[1343, 11], [1343], [
      .prior 4108 false [],
      .prior 4094 true [11],
      .equation 139 false false
        [1341, 10]
        [12, 10, 12],
      .prior 4107 false [12, 10, 12],
      .equation 10 true false
        [1289, 12]
        [10, 12],
      .prior 3532 false [10, 12],
      .equation 8 true false
        [1289, 10]
        [12],
      .equation 707 true false
        []
        [12],
      .equation 10 true false
        [1341, 12]
        [],
      .equation 708 true false
        []
        [],
      .prior 4096 false []]⟩,
    ⟨[1345, 15], [1343], [
      .equation 709 false false
        []
        [15],
      .equation 12 false false
        [1343]
        []]⟩,
    ⟨[1343, 15], [1345], [
      .equation 709 true false
        []
        []]⟩,
    ⟨[1345, 3], [1345, 3], [
]⟩,
    ⟨[1345], [1345], [
]⟩,
    ⟨[1345, 3], [1345], [
      .prior 4112 false [],
      .prior 4111 true [3],
      .equation 36 false false
        [1343, 2]
        [14],
      .equation 4 true false
        [1343, 2]
        [14],
      .prior 4100 false [14],
      .equation 12 true false
        [1343, 14]
        [],
      .equation 709 true false
        []
        [],
      .prior 4113 false []]⟩,
    ⟨[1345, 5], [1345, 5], [
]⟩,
    ⟨[1345, 5], [1345], [
      .prior 4115 false [],
      .prior 4111 true [5],
      .equation 30 false false
        [1343, 4]
        [14],
      .equation 6 true false
        [1343, 4]
        [14],
      .prior 4103 false [14],
      .equation 12 true false
        [1343, 14]
        [],
      .equation 709 true false
        []
        [],
      .prior 4113 false []]⟩,
    ⟨[1345, 9], [1345, 9], [
]⟩,
    ⟨[1345, 9], [1345], [
      .prior 4117 false [],
      .prior 4111 true [9],
      .equation 13 false false
        [1343, 8]
        [14],
      .equation 1 true false
        [1343, 8]
        [14],
      .prior 4106 false [14],
      .equation 12 true false
        [1343, 14]
        [],
      .equation 709 true false
        []
        [],
      .prior 4113 false []]⟩,
    ⟨[1345, 11], [1345, 11], [
]⟩,
    ⟨[1345, 11], [1345], [
      .prior 4119 false [],
      .prior 4111 true [11],
      .equation 136 false false
        [1343, 10]
        [14],
      .equation 8 true false
        [1343, 10]
        [14],
      .prior 4109 false [14],
      .equation 12 true false
        [1343, 14]
        [],
      .equation 709 true false
        []
        [],
      .prior 4113 false []]⟩,
    ⟨[1345, 17], [1347], [
      .equation 710 true false
        []
        []]⟩,
    ⟨[1345, 17], [1347], [
      .prior 4121 false []]⟩,
    ⟨[1347], [1347], [
]⟩,
    ⟨[1349, 1], [1347], [
      .equation 711 false false
        []
        [1],
      .equation 2 false false
        [1347]
        []]⟩,
    ⟨[1347, 1], [1349], [
      .equation 711 true false
        []
        []]⟩,
    ⟨[1349, 5], [1349, 5], [
]⟩,
    ⟨[1349], [1349], [
]⟩,
    ⟨[1349, 5], [1349], [
      .prior 4126 false [],
      .prior 4125 true [5],
      .equation 26 false false
        [1347]
        [4, 0],
      .equation 6 true false
        [1347, 4]
        [0],
      .prior 4122 true [5, 0],
      .equation 31 false false
        [1345, 4]
        [16, 0],
      .equation 6 true false
        [1345, 4]
        [16, 0],
      .prior 4116 false [16, 0],
      .equation 14 true false
        [1345, 16]
        [0],
      .equation 710 true false
        []
        [0],
      .prior 4123 false [0],
      .equation 2 true false
        [1347, 0]
        [],
      .equation 711 true false
        []
        [],
      .prior 4127 false []]⟩,
    ⟨[1349, 9], [1349, 9], [
]⟩,
    ⟨[1349, 9], [1349], [
      .prior 4129 false [],
      .prior 4125 true [9],
      .equation 3 false false
        [1347]
        [8, 0],
      .equation 1 true false
        [1347, 8]
        [0],
      .prior 4122 true [9, 0],
      .equation 15 false false
        [1345, 8]
        [16, 0],
      .equation 1 true false
        [1345, 8]
        [16, 0],
      .prior 4118 false [16, 0],
      .equation 14 true false
        [1345, 16]
        [0],
      .equation 710 true false
        []
        [0],
      .prior 4123 false [0],
      .equation 2 true false
        [1347, 0]
        [],
      .equation 711 true false
        []
        [],
      .prior 4127 false []]⟩,
    ⟨[1351, 3], [1349], [
      .equation 712 false false
        []
        [3],
      .equation 4 false false
        [1349]
        []]⟩,
    ⟨[1349, 3], [1351], [
      .equation 712 true false
        []
        []]⟩,
    ⟨[1351, 1], [1351, 1], [
]⟩,
    ⟨[1351], [1351], [
]⟩,
    ⟨[1351, 1], [1351], [
      .prior 4133 false [],
      .prior 4132 true [1],
      .equation 39 false false
        [1349, 0]
        [2, 0, 2],
      .equation 2 true false
        [1349, 0]
        [2, 0, 2],
      .prior 4124 false [2, 0, 2],
      .equation 4 true false
        [1347, 2]
        [0, 2],
      .prior 4122 true [3, 0, 2],
      .equation 37 false false
        [1345, 2]
        [16, 0, 2],
      .equation 4 true false
        [1345, 2]
        [16, 0, 2],
      .prior 4114 false [16, 0, 2],
      .equation 14 true false
        [1345, 16]
        [0, 2],
      .equation 710 true false
        []
        [0, 2],
      .prior 4123 false [0, 2],
      .equation 2 true false
        [1347, 0]
        [2],
      .equation 711 true false
        []
        [2],
      .equation 4 true false
        [1349, 2]
        [],
      .equation 712 true false
        []
        [],
      .prior 4134 false []]⟩,
    ⟨[1351, 9], [1351, 9], [
]⟩,
    ⟨[1351, 9], [1351], [
      .prior 4136 false [],
      .prior 4132 true [9],
      .equation 5 false false
        [1349]
        [8, 2],
      .equation 1 true false
        [1349, 8]
        [2],
      .prior 4130 false [2],
      .equation 4 true false
        [1349, 2]
        [],
      .equation 712 true false
        []
        [],
      .prior 4134 false []]⟩,
    ⟨[1353, 5], [1351], [
      .equation 713 false false
        []
        [5],
      .equation 6 false false
        [1351]
        []]⟩,
    ⟨[1351, 5], [1353], [
      .equation 713 true false
        []
        []]⟩,
    ⟨[1353, 1], [1353, 1], [
]⟩,
    ⟨[1353], [1353], [
]⟩,
    ⟨[1353, 1], [1353], [
      .prior 4140 false [],
      .prior 4139 true [1],
      .equation 26 false false
        [1351, 0]
        [4],
      .equation 2 true false
        [1351, 0]
        [4],
      .prior 4135 false [4],
      .equation 6 true false
        [1351, 4]
        [],
      .equation 713 true false
        []
        [],
      .prior 4141 false []]⟩,
    ⟨[1353, 3], [1353, 3], [
]⟩,
    ⟨[1353, 3], [1353], [
      .prior 4143 false [],
      .prior 4139 true [3],
      .equation 33 false false
        [1351, 2]
        [4, 2, 4],
      .equation 4 true false
        [1351, 2]
        [4, 2, 4],
      .prior 4131 false [4, 2, 4],
      .equation 6 true false
        [1349, 4]
        [2, 4],
      .prior 4128 false [2, 4],
      .equation 4 true false
        [1349, 2]
        [4],
      .equation 712 true false
        []
        [4],
      .equation 6 true false
        [1351, 4]
        [],
      .equation 713 true false
        []
        [],
      .prior 4141 false []]⟩,
    ⟨[1353, 9], [1353, 9], [
]⟩,
    ⟨[1353, 9], [1353], [
      .prior 4145 false [],
      .prior 4139 true [9],
      .equation 7 false false
        [1351]
        [8, 4],
      .equation 1 true false
        [1351, 8]
        [4],
      .prior 4137 false [4],
      .equation 6 true false
        [1351, 4]
        [],
      .equation 713 true false
        []
        [],
      .prior 4141 false []]⟩,
    ⟨[1353, 11], [1355], [
      .equation 714 true false
        []
        []]⟩,
    ⟨[1357, 8, 0], [1359], [
      .equation 1 true false
        [1357, 8]
        [0],
      .equation 715 false false
        []
        [9, 0],
      .equation 11 false false
        [1355, 8]
        [12, 0],
      .equation 1 true false
        [1355, 8]
        [12, 0],
      .prior 4147 true [9, 12, 0],
      .equation 9 false false
        [1353, 8]
        [10, 12, 0],
      .equation 1 true false
        [1353, 8]
        [10, 12, 0],
      .prior 4146 false [10, 12, 0],
      .equation 8 true false
        [1353, 10]
        [12, 0],
      .equation 714 true false
        []
        [12, 0],
      .equation 10 true false
        [1355, 12]
        [0],
      .equation 715 true false
        []
        [0],
      .equation 2 true false
        [1357, 0]
        [],
      .equation 716 true false
        []
        []]⟩,
    ⟨[1361], [1361], [
]⟩,
    ⟨[1363, 9], [1363], [
      .equation 718 false false
        []
        [9],
      .equation 15 false false
        [1361, 8]
        [16],
      .equation 1 true false
        [1361, 8]
        [16],
      .equation 717 false false
        []
        [9, 16],
      .equation 13 false false
        [1359, 8]
        [14, 16],
      .equation 1 true false
        [1359, 8]
        [14, 16],
      .equation 716 false false
        []
        [9, 14, 16],
      .equation 3 false false
        [1357]
        [8, 0, 14, 16],
      .prior 4148 false [14, 16],
      .equation 12 true false
        [1359, 14]
        [16],
      .equation 717 true false
        []
        [16],
      .prior 4149 false [16],
      .equation 14 true false
        [1361, 16]
        [],
      .equation 718 true false
        []
        []]⟩,
    ⟨[1367, 8, 4], [1367, 5], [
      .equation 1 true false
        [1367, 8]
        [4],
      .equation 720 false false
        []
        [9, 4],
      .equation 5 false false
        [1365]
        [8, 2, 4],
      .equation 1 true false
        [1365, 8]
        [2, 4],
      .equation 719 false false
        []
        [9, 2, 4],
      .equation 3 false false
        [1363]
        [8, 0, 2, 4],
      .equation 1 true false
        [1363, 8]
        [0, 2, 4],
      .prior 4150 false [0, 2, 4],
      .equation 2 true false
        [1363, 0]
        [2, 4],
      .equation 719 true false
        []
        [2, 4],
      .equation 4 true false
        [1365, 2]
        [4],
      .equation 720 true false
        []
        [4],
      .equation 6 true false
        [1367, 4]
        []]⟩,
    ⟨[1373, 9], [1373], [
      .equation 723 false false
        []
        [9],
      .equation 9 false false
        [1371, 8]
        [10],
      .equation 1 true false
        [1371, 8]
        [10],
      .equation 722 false false
        []
        [9, 10],
      .equation 3 false false
        [1369]
        [8, 0, 10],
      .equation 1 true false
        [1369, 8]
        [0, 10],
      .equation 721 false false
        []
        [9, 0, 10],
      .equation 7 false false
        [1367]
        [8, 4, 0, 10],
      .prior 4151 false [0, 10],
      .equation 721 true false
        []
        [0, 10],
      .equation 2 true false
        [1369, 0]
        [10],
      .equation 722 true false
        []
        [10],
      .equation 8 true false
        [1371, 10]
        [],
      .equation 723 true false
        []
        []]⟩,
    ⟨[1377, 8, 14], [1377, 15], [
      .equation 1 true false
        [1377, 8]
        [14],
      .equation 725 false false
        []
        [9, 14],
      .equation 3 false false
        [1375]
        [8, 0, 14],
      .equation 1 true false
        [1375, 8]
        [0, 14],
      .equation 724 false false
        []
        [9, 0, 14],
      .equation 11 false false
        [1373, 8]
        [12, 0, 14],
      .equation 1 true false
        [1373, 8]
        [12, 0, 14],
      .prior 4152 false [12, 0, 14],
      .equation 10 true false
        [1373, 12]
        [0, 14],
      .equation 724 true false
        []
        [0, 14],
      .equation 2 true false
        [1375, 0]
        [14],
      .equation 725 true false
        []
        [14],
      .equation 12 true false
        [1377, 14]
        []]⟩,
    ⟨[1383, 9], [1383], [
      .equation 728 false false
        []
        [9],
      .equation 3 false false
        [1381]
        [8, 0],
      .equation 1 true false
        [1381, 8]
        [0],
      .equation 727 false false
        []
        [9, 0],
      .equation 15 false false
        [1379, 8]
        [16, 0],
      .equation 1 true false
        [1379, 8]
        [16, 0],
      .equation 726 false false
        []
        [9, 16, 0],
      .equation 13 false false
        [1377, 8]
        [14, 16, 0],
      .prior 4153 false [16, 0],
      .equation 726 true false
        []
        [16, 0],
      .equation 14 true false
        [1379, 16]
        [0],
      .equation 727 true false
        []
        [0],
      .equation 2 true false
        [1381, 0]
        [],
      .equation 728 true false
        []
        []]⟩,
    ⟨[1387, 8, 0], [1387, 1], [
      .equation 1 true false
        [1387, 8]
        [0],
      .equation 730 false false
        []
        [9, 0],
      .equation 7 false false
        [1385]
        [8, 4, 0],
      .equation 1 true false
        [1385, 8]
        [4, 0],
      .equation 729 false false
        []
        [9, 4, 0],
      .equation 5 false false
        [1383]
        [8, 2, 4, 0],
      .equation 1 true false
        [1383, 8]
        [2, 4, 0],
      .prior 4154 false [2, 4, 0],
      .equation 4 true false
        [1383, 2]
        [4, 0],
      .equation 729 true false
        []
        [4, 0],
      .equation 6 true false
        [1385, 4]
        [0],
      .equation 730 true false
        []
        [0],
      .equation 2 true false
        [1387, 0]
        []]⟩,
    ⟨[1393, 9], [1393], [
      .equation 733 false false
        []
        [9],
      .equation 11 false false
        [1391, 8]
        [12],
      .equation 1 true false
        [1391, 8]
        [12],
      .equation 732 false false
        []
        [9, 12],
      .equation 9 false false
        [1389, 8]
        [10, 12],
      .equation 1 true false
        [1389, 8]
        [10, 12],
      .equation 731 false false
        []
        [9, 10, 12],
      .equation 3 false false
        [1387]
        [8, 0, 10, 12],
      .prior 4155 false [10, 12],
      .equation 731 true false
        []
        [10, 12],
      .equation 8 true false
        [1389, 10]
        [12],
      .equation 732 true false
        []
        [12],
      .equation 10 true false
        [1391, 12]
        [],
      .equation 733 true false
        []
        []]⟩,
    ⟨[1397, 8, 16], [1397, 17], [
      .equation 1 true false
        [1397, 8]
        [16],
      .equation 735 false false
        []
        [9, 16],
      .equation 13 false false
        [1395, 8]
        [14, 16],
      .equation 1 true false
        [1395, 8]
        [14, 16],
      .equation 734 false false
        []
        [9, 14, 16],
      .equation 3 false false
        [1393]
        [8, 0, 14, 16],
      .equation 1 true false
        [1393, 8]
        [0, 14, 16],
      .prior 4156 false [0, 14, 16],
      .equation 2 true false
        [1393, 0]
        [14, 16],
      .equation 734 true false
        []
        [14, 16],
      .equation 12 true false
        [1395, 14]
        [16],
      .equation 735 true false
        []
        [16],
      .equation 14 true false
        [1397, 16]
        []]⟩,
    ⟨[1403, 9], [1403], [
      .equation 738 false false
        []
        [9],
      .equation 5 false false
        [1401]
        [8, 2],
      .equation 1 true false
        [1401, 8]
        [2],
      .equation 737 false false
        []
        [9, 2],
      .equation 3 false false
        [1399]
        [8, 0, 2],
      .equation 1 true false
        [1399, 8]
        [0, 2],
      .equation 736 false false
        []
        [9, 0, 2],
      .equation 15 false false
        [1397, 8]
        [16, 0, 2],
      .prior 4157 false [0, 2],
      .equation 736 true false
        []
        [0, 2],
      .equation 2 true false
        [1399, 0]
        [2],
      .equation 737 true false
        []
        [2],
      .equation 4 true false
        [1401, 2]
        [],
      .equation 738 true false
        []
        []]⟩,
    ⟨[1407, 8, 10], [1407, 11], [
      .equation 1 true false
        [1407, 8]
        [10],
      .equation 740 false false
        []
        [9, 10],
      .equation 3 false false
        [1405]
        [8, 0, 10],
      .equation 1 true false
        [1405, 8]
        [0, 10],
      .equation 739 false false
        []
        [9, 0, 10],
      .equation 7 false false
        [1403]
        [8, 4, 0, 10],
      .equation 1 true false
        [1403, 8]
        [4, 0, 10],
      .prior 4158 false [4, 0, 10],
      .equation 6 true false
        [1403, 4]
        [0, 10],
      .equation 739 true false
        []
        [0, 10],
      .equation 2 true false
        [1405, 0]
        [10],
      .equation 740 true false
        []
        [10],
      .equation 8 true false
        [1407, 10]
        []]⟩,
    ⟨[1413, 9], [1413], [
      .equation 743 false false
        []
        [9],
      .equation 3 false false
        [1411]
        [8, 0],
      .equation 1 true false
        [1411, 8]
        [0],
      .equation 742 false false
        []
        [9, 0],
      .equation 11 false false
        [1409, 8]
        [12, 0],
      .equation 1 true false
        [1409, 8]
        [12, 0],
      .equation 741 false false
        []
        [9, 12, 0],
      .equation 9 false false
        [1407, 8]
        [10, 12, 0],
      .prior 4159 false [12, 0],
      .equation 741 true false
        []
        [12, 0],
      .equation 10 true false
        [1409, 12]
        [0],
      .equation 742 true false
        []
        [0],
      .equation 2 true false
        [1411, 0]
        [],
      .equation 743 true false
        []
        []]⟩,
    ⟨[1413], [1413], [
]⟩,
    ⟨[1415, 15], [1413], [
      .equation 744 false false
        []
        [15],
      .equation 12 false false
        [1413]
        []]⟩,
    ⟨[1417, 17], [1415], [
      .equation 745 false false
        []
        [17],
      .equation 14 false false
        [1415]
        []]⟩,
    ⟨[1417], [1417], [
]⟩,
    ⟨[1419, 1], [1417], [
      .equation 746 false false
        []
        [1],
      .equation 2 false false
        [1417]
        []]⟩,
    ⟨[1417, 8, 0], [1417, 1], [
      .equation 1 true false
        [1417, 8]
        [0],
      .equation 745 false false
        []
        [9, 0],
      .equation 15 false false
        [1415, 8]
        [16, 0],
      .equation 1 true false
        [1415, 8]
        [16, 0],
      .equation 744 false false
        []
        [9, 16, 0],
      .equation 13 false false
        [1413, 8]
        [14, 16, 0],
      .equation 1 true false
        [1413, 8]
        [14, 16, 0],
      .prior 4160 false [14, 16, 0],
      .prior 4161 false [14, 16, 0],
      .equation 12 true false
        [1413, 14]
        [16, 0],
      .equation 744 true false
        []
        [16, 0],
      .equation 14 true false
        [1415, 16]
        [0],
      .equation 745 true false
        []
        [0],
      .prior 4164 false [0],
      .equation 2 true false
        [1417, 0]
        []]⟩,
    ⟨[1421, 3], [1419], [
      .equation 747 false false
        []
        [3],
      .equation 4 false false
        [1419]
        []]⟩,
    ⟨[1421], [1421], [
]⟩,
    ⟨[1423, 5], [1421], [
      .equation 748 false false
        []
        [5],
      .equation 6 false false
        [1421]
        []]⟩,
    ⟨[1423, 9], [1423], [
      .equation 748 false false
        []
        [9],
      .equation 7 false false
        [1421]
        [8, 4],
      .equation 1 true false
        [1421, 8]
        [4],
      .equation 747 false false
        []
        [9, 4],
      .equation 5 false false
        [1419]
        [8, 2, 4],
      .equation 1 true false
        [1419, 8]
        [2, 4],
      .equation 746 false false
        []
        [9, 2, 4],
      .equation 3 false false
        [1417]
        [8, 0, 2, 4],
      .prior 4166 false [2, 4],
      .equation 746 true false
        []
        [2, 4],
      .equation 4 true false
        [1419, 2]
        [4],
      .equation 747 true false
        []
        [4],
      .prior 4168 false [4],
      .equation 6 true false
        [1421, 4]
        [],
      .equation 748 true false
        []
        []]⟩,
    ⟨[1425, 1], [1423], [
      .equation 749 false false
        []
        [1],
      .equation 2 false false
        [1423]
        []]⟩,
    ⟨[1425], [1425], [
]⟩,
    ⟨[1427, 11], [1425], [
      .equation 750 false false
        []
        [11],
      .equation 8 false false
        [1425]
        []]⟩,
    ⟨[1427], [1427], [
]⟩,
    ⟨[1429, 13], [1427], [
      .equation 751 false false
        []
        [13],
      .equation 10 false false
        [1427]
        []]⟩,
    ⟨[1431, 1], [1429], [
      .equation 752 false false
        []
        [1],
      .equation 2 false false
        [1429]
        []]⟩,
    ⟨[1431], [1431], [
]⟩,
    ⟨[1433, 15], [1431], [
      .equation 753 false false
        []
        [15],
      .equation 12 false false
        [1431]
        []]⟩,
    ⟨[1433], [1433], [
]⟩,
    ⟨[1435, 17], [1433], [
      .equation 754 false false
        []
        [17],
      .equation 14 false false
        [1433]
        []]⟩,
    ⟨[1435], [1435], [
]⟩,
    ⟨[1437, 1], [1435], [
      .equation 755 false false
        []
        [1],
      .equation 2 false false
        [1435]
        []]⟩,
    ⟨[1437], [1437], [
]⟩,
    ⟨[1439, 3], [1437], [
      .equation 756 false false
        []
        [3],
      .equation 4 false false
        [1437]
        []]⟩,
    ⟨[1439], [1439], [
]⟩,
    ⟨[1441, 5], [1439], [
      .equation 757 false false
        []
        [5],
      .equation 6 false false
        [1439]
        []]⟩,
    ⟨[1441], [1441], [
]⟩,
    ⟨[
      1441, 4, 2, 0, 16, 14, 0, 12
    ], [1429, 12], [
      .equation 6 true false
        [1441, 4]
        [2, 0, 16, 14, 0, 12],
      .prior 4186 false [2, 0, 16, 14, 0, 12],
      .equation 4 true false
        [1439, 2]
        [0, 16, 14, 0, 12],
      .prior 4184 false [0, 16, 14, 0, 12],
      .equation 2 true false
        [1437, 0]
        [16, 14, 0, 12],
      .prior 4182 false [16, 14, 0, 12],
      .equation 14 true false
        [1435, 16]
        [14, 0, 12],
      .prior 4180 false [14, 0, 12],
      .equation 12 true false
        [1433, 14]
        [0, 12],
      .prior 4178 false [0, 12],
      .equation 2 true false
        [1431, 0]
        [12],
      .prior 4176 false [12]]⟩,
    ⟨[
      1441, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16
    ], [1417, 17], [
      .prior 4188 false [10, 0, 4, 2, 0, 16],
      .equation 10 true false
        [1429, 12]
        [10, 0, 4, 2, 0, 16],
      .prior 4175 false [10, 0, 4, 2, 0, 16],
      .equation 8 true false
        [1427, 10]
        [0, 4, 2, 0, 16],
      .prior 4173 false [0, 4, 2, 0, 16],
      .equation 2 true false
        [1425, 0]
        [4, 2, 0, 16],
      .prior 4171 false [4, 2, 0, 16],
      .equation 6 true false
        [1423, 4]
        [2, 0, 16],
      .prior 4169 false [2, 0, 16],
      .equation 4 true false
        [1421, 2]
        [0, 16],
      .prior 4167 false [0, 16],
      .equation 2 true false
        [1419, 0]
        [16],
      .prior 4165 false [16],
      .equation 14 true false
        [1417, 16]
        []]⟩,
    ⟨[
      1441, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4
    ], [1403], [
      .prior 4189 false [14, 0, 12, 10, 0, 4],
      .prior 4163 false [14, 0, 12, 10, 0, 4],
      .equation 12 true false
        [1415, 14]
        [0, 12, 10, 0, 4],
      .prior 4162 false [0, 12, 10, 0, 4],
      .equation 2 true false
        [1413, 0]
        [12, 10, 0, 4],
      .equation 743 false false
        []
        [1, 12, 10, 0, 4],
      .equation 2 false false
        [1411]
        [12, 10, 0, 4],
      .equation 10 true false
        [1411, 12]
        [10, 0, 4],
      .equation 742 false false
        []
        [13, 10, 0, 4],
      .equation 10 false false
        [1409]
        [10, 0, 4],
      .equation 8 true false
        [1409, 10]
        [0, 4],
      .equation 741 false false
        []
        [11, 0, 4],
      .equation 8 false false
        [1407]
        [0, 4],
      .equation 2 true false
        [1407, 0]
        [4],
      .equation 740 false false
        []
        [1, 4],
      .equation 2 false false
        [1405]
        [4],
      .equation 6 true false
        [1405, 4]
        [],
      .equation 739 false false
        []
        [5],
      .equation 6 false false
        [1403]
        []]⟩,
    ⟨[
      1441, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12
    ], [1391], [
      .prior 4190 false [2, 0, 16, 14, 0, 12],
      .equation 4 true false
        [1403, 2]
        [0, 16, 14, 0, 12],
      .equation 738 false false
        []
        [3, 0, 16, 14, 0, 12],
      .equation 4 false false
        [1401]
        [0, 16, 14, 0, 12],
      .equation 2 true false
        [1401, 0]
        [16, 14, 0, 12],
      .equation 737 false false
        []
        [1, 16, 14, 0, 12],
      .equation 2 false false
        [1399]
        [16, 14, 0, 12],
      .equation 14 true false
        [1399, 16]
        [14, 0, 12],
      .equation 736 false false
        []
        [17, 14, 0, 12],
      .equation 14 false false
        [1397]
        [14, 0, 12],
      .equation 12 true false
        [1397, 14]
        [0, 12],
      .equation 735 false false
        []
        [15, 0, 12],
      .equation 12 false false
        [1395]
        [0, 12],
      .equation 2 true false
        [1395, 0]
        [12],
      .equation 734 false false
        []
        [1, 12],
      .equation 2 false false
        [1393]
        [12],
      .equation 10 true false
        [1393, 12]
        [],
      .equation 733 false false
        []
        [13],
      .equation 10 false false
        [1391]
        []]⟩,
    ⟨[
      1441, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16
    ], [1379], [
      .prior 4191 false [10, 0, 4, 2, 0, 16],
      .equation 8 true false
        [1391, 10]
        [0, 4, 2, 0, 16],
      .equation 732 false false
        []
        [11, 0, 4, 2, 0, 16],
      .equation 8 false false
        [1389]
        [0, 4, 2, 0, 16],
      .equation 2 true false
        [1389, 0]
        [4, 2, 0, 16],
      .equation 731 false false
        []
        [1, 4, 2, 0, 16],
      .equation 2 false false
        [1387]
        [4, 2, 0, 16],
      .equation 6 true false
        [1387, 4]
        [2, 0, 16],
      .equation 730 false false
        []
        [5, 2, 0, 16],
      .equation 6 false false
        [1385]
        [2, 0, 16],
      .equation 4 true false
        [1385, 2]
        [0, 16],
      .equation 729 false false
        []
        [3, 0, 16],
      .equation 4 false false
        [1383]
        [0, 16],
      .equation 2 true false
        [1383, 0]
        [16],
      .equation 728 false false
        []
        [1, 16],
      .equation 2 false false
        [1381]
        [16],
      .equation 14 true false
        [1381, 16]
        [],
      .equation 727 false false
        []
        [17],
      .equation 14 false false
        [1379]
        []]⟩,
    ⟨[
      1441, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4
    ], [1367], [
      .prior 4192 false [14, 0, 12, 10, 0, 4],
      .equation 12 true false
        [1379, 14]
        [0, 12, 10, 0, 4],
      .equation 726 false false
        []
        [15, 0, 12, 10, 0, 4],
      .equation 12 false false
        [1377]
        [0, 12, 10, 0, 4],
      .equation 2 true false
        [1377, 0]
        [12, 10, 0, 4],
      .equation 725 false false
        []
        [1, 12, 10, 0, 4],
      .equation 2 false false
        [1375]
        [12, 10, 0, 4],
      .equation 10 true false
        [1375, 12]
        [10, 0, 4],
      .equation 724 false false
        []
        [13, 10, 0, 4],
      .equation 10 false false
        [1373]
        [10, 0, 4],
      .equation 8 true false
        [1373, 10]
        [0, 4],
      .equation 723 false false
        []
        [11, 0, 4],
      .equation 8 false false
        [1371]
        [0, 4],
      .equation 2 true false
        [1371, 0]
        [4],
      .equation 722 false false
        []
        [1, 4],
      .equation 2 false false
        [1369]
        [4],
      .equation 6 true false
        [1369, 4]
        [],
      .equation 721 false false
        []
        [5],
      .equation 6 false false
        [1367]
        []]⟩,
    ⟨[
      1441, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12
    ], [1355], [
      .prior 4193 false [2, 0, 16, 14, 0, 12],
      .equation 4 true false
        [1367, 2]
        [0, 16, 14, 0, 12],
      .equation 720 false false
        []
        [3, 0, 16, 14, 0, 12],
      .equation 4 false false
        [1365]
        [0, 16, 14, 0, 12],
      .equation 2 true false
        [1365, 0]
        [16, 14, 0, 12],
      .equation 719 false false
        []
        [1, 16, 14, 0, 12],
      .equation 2 false false
        [1363]
        [16, 14, 0, 12],
      .equation 14 true false
        [1363, 16]
        [14, 0, 12],
      .equation 718 false false
        []
        [17, 14, 0, 12],
      .equation 14 false false
        [1361]
        [14, 0, 12],
      .equation 12 true false
        [1361, 14]
        [0, 12],
      .equation 717 false false
        []
        [15, 0, 12],
      .equation 12 false false
        [1359]
        [0, 12],
      .equation 2 true false
        [1359, 0]
        [12],
      .equation 716 false false
        []
        [1, 12],
      .equation 2 false false
        [1357]
        [12],
      .equation 10 true false
        [1357, 12]
        [],
      .equation 715 false false
        []
        [13],
      .equation 10 false false
        [1355]
        []]⟩,
    ⟨[
      1441, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16
    ], [1345], [
      .prior 4194 false [10, 0, 4, 2, 0, 16],
      .equation 8 true false
        [1355, 10]
        [0, 4, 2, 0, 16],
      .equation 714 false false
        []
        [11, 0, 4, 2, 0, 16],
      .equation 8 false false
        [1353]
        [0, 4, 2, 0, 16],
      .equation 2 true false
        [1353, 0]
        [4, 2, 0, 16],
      .prior 4142 false [4, 2, 0, 16],
      .equation 6 true false
        [1353, 4]
        [2, 0, 16],
      .prior 4138 false [2, 0, 16],
      .equation 4 true false
        [1351, 2]
        [0, 16],
      .prior 4131 false [0, 16],
      .equation 2 true false
        [1349, 0]
        [16],
      .prior 4124 false [16],
      .equation 14 true false
        [1347, 16]
        [],
      .equation 710 false false
        []
        [17],
      .equation 14 false false
        [1345]
        []]⟩,
    ⟨[
      1441, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2
    ], [1339, 2], [
      .prior 4195 false [
        14, 0, 12, 10, 0, 4, 2
      ],
      .equation 12 true false
        [1345, 14]
        [0, 12, 10, 0, 4, 2],
      .prior 4110 false [0, 12, 10, 0, 4, 2],
      .equation 2 true false
        [1343, 0]
        [12, 10, 0, 4, 2],
      .prior 4097 false [12, 10, 0, 4, 2],
      .equation 10 true false
        [1343, 12]
        [10, 0, 4, 2],
      .prior 4093 false [10, 0, 4, 2],
      .equation 8 true false
        [1341, 10]
        [0, 4, 2],
      .prior 4079 false [0, 4, 2],
      .equation 2 true false
        [1289, 0]
        [4, 2],
      .prior 4075 false [4, 2],
      .equation 6 true false
        [1339, 4]
        [2],
      .prior 4078 false [2]]⟩,
    ⟨[
      1441, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10
    ], [45, 11], [
      .prior 4196 false [0, 16, 14, 0, 12, 10],
      .equation 4 true false
        [1339, 2]
        [0, 16, 14, 0, 12, 10],
      .prior 4058 false [0, 16, 14, 0, 12, 10],
      .equation 2 true false
        [1337, 0]
        [16, 14, 0, 12, 10],
      .prior 4018 false [16, 14, 0, 12, 10],
      .equation 14 true false
        [1337, 16]
        [14, 0, 12, 10],
      .prior 4014 false [14, 0, 12, 10],
      .equation 12 true false
        [181, 14]
        [0, 12, 10],
      .prior 427 false [0, 12, 10],
      .equation 2 true false
        [185, 0]
        [12, 10],
      .prior 384 false [12, 10],
      .equation 10 true false
        [45, 12]
        [10],
      .equation 52 true false
        []
        [10],
      .prior 388 false [10],
      .equation 8 true false
        [45, 10]
        []]⟩,
    ⟨[
      1441, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14
    ], [215], [
      .prior 4197 false [0, 4, 2, 0, 16, 14],
      .prior 1700 false [0, 4, 2, 0, 16, 14],
      .equation 2 true false
        [1003, 0]
        [4, 2, 0, 16, 14],
      .prior 1685 false [4, 2, 0, 16, 14],
      .equation 6 true false
        [1003, 4]
        [2, 0, 16, 14],
      .prior 1691 false [2, 0, 16, 14],
      .equation 4 true false
        [39, 2]
        [0, 16, 14],
      .prior 136 false [0, 16, 14],
      .equation 2 true false
        [37, 0]
        [16, 14],
      .prior 124 false [16, 14],
      .equation 14 true false
        [35, 16]
        [14],
      .equation 142 true false
        []
        [14],
      .equation 12 true false
        [215, 14]
        [],
      .prior 551 false []]⟩,
    ⟨[
      1441, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2
    ], [611], [
      .prior 4198 false [0, 12, 10, 0, 4, 2],
      .equation 2 true false
        [215, 0]
        [12, 10, 0, 4, 2],
      .equation 144 true false
        []
        [12, 10, 0, 4, 2],
      .equation 10 true false
        [217, 12]
        [10, 0, 4, 2],
      .prior 3205 false [10, 0, 4, 2],
      .equation 8 true false
        [1181, 10]
        [0, 4, 2],
      .prior 3202 false [0, 4, 2],
      .equation 2 true false
        [1181, 0]
        [4, 2],
      .prior 3190 false [4, 2],
      .equation 6 true false
        [611, 4]
        [2],
      .prior 1145 false [2],
      .equation 4 true false
        [611, 2]
        [],
      .prior 1143 false []]⟩,
    ⟨[
      1441, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0
    ], [35, 0], [
      .prior 4199 false [
        0, 16, 14, 0, 12, 10, 0
      ],
      .equation 2 true false
        [611, 0]
        [16, 14, 0, 12, 10, 0],
      .prior 3191 false [16, 14, 0, 12, 10, 0],
      .equation 14 true false
        [1181, 16]
        [14, 0, 12, 10, 0],
      .prior 3187 false [14, 0, 12, 10, 0],
      .equation 12 true false
        [203, 14]
        [0, 12, 10, 0],
      .prior 299 false [0, 12, 10, 0],
      .equation 2 true false
        [203, 0]
        [12, 10, 0],
      .prior 295 false [12, 10, 0],
      .equation 10 true false
        [33, 12]
        [10, 0],
      .equation 46 true false
        []
        [10, 0],
      .equation 8 true false
        [35, 10]
        [0],
      .prior 312 false [0]]⟩,
    ⟨[
      1441, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0
    ], [615, 1], [
      .prior 4200 false [4, 2, 0, 16, 14, 0],
      .equation 2 true false
        [35, 0]
        [4, 2, 0, 16, 14, 0],
      .equation 47 true false
        []
        [4, 2, 0, 16, 14, 0],
      .equation 6 true false
        [37, 4]
        [2, 0, 16, 14, 0],
      .prior 129 false [2, 0, 16, 14, 0],
      .equation 4 true false
        [37, 2]
        [0, 16, 14, 0],
      .equation 48 true false
        []
        [0, 16, 14, 0],
      .equation 2 true false
        [39, 0]
        [16, 14, 0],
      .prior 140 false [16, 14, 0],
      .equation 14 true false
        [39, 16]
        [14, 0],
      .prior 579 false [14, 0],
      .equation 12 true false
        [219, 14]
        [0],
      .prior 1179 false [0],
      .equation 2 true false
        [615, 0]
        []]⟩,
    ⟨[1443, 11], [315], [
      .equation 758 false false
        []
        [11],
      .equation 198 false false
        [1441, 4, 2, 0]
        [
          16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0,
          12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0,
          4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0,
          16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0,
          12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0,
          4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0,
          16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0,
          12
        ],
      .prior 4201 false [12],
      .prior 1188 false [12],
      .equation 10 true false
        [313, 12]
        [],
      .equation 193 true false
        []
        [],
      .prior 802 false []]⟩,
    ⟨[315, 11], [1443], [
      .prior 4202 true [11],
      .equation 8 false false
        [1443]
        []]⟩,
    ⟨[1441, 11], [1441, 11], [
]⟩,
    ⟨[1441, 11], [315], [
      .prior 4204 false [],
      .equation 2 true false
        [1441]
        [11],
      .equation 758 true false
        []
        [1, 11],
      .equation 43 false false
        [1443]
        [10, 0, 10, 0],
      .equation 8 true false
        [1443, 10]
        [0, 10, 0],
      .prior 4202 false [0, 10, 0],
      .equation 2 true false
        [315, 0]
        [10, 0],
      .equation 194 true false
        []
        [10, 0],
      .equation 8 true false
        [317, 10]
        [0],
      .prior 875 false [0],
      .equation 2 true false
        [317, 0]
        [],
      .prior 804 false [],
      .prior 802 false []]⟩,
    ⟨[315, 11], [1443], [
      .prior 4203 false []]⟩,
    ⟨[1443], [1441], [
      .prior 4206 true [],
      .prior 4205 true [11],
      .equation 8 false false
        [1441]
        []]⟩,
    ⟨[1441, 11], [315], [
      .prior 4204 false [],
      .prior 4205 false []]⟩,
    ⟨[1441, 3], [1441], [
      .prior 4207 true [3],
      .prior 4203 true [3],
      .prior 1198 true [11, 3],
      .prior 4208 true [3, 11, 3],
      .equation 34 false false
        [1441, 2]
        [3],
      .prior 4187 false []]⟩,
    ⟨[1441, 7], [1441], [
      .prior 4207 true [7],
      .prior 4203 true [7],
      .prior 886 true [11, 7],
      .prior 4208 true [7, 11, 7],
      .equation 21 false false
        [1441, 6]
        [7],
      .prior 4187 false []]⟩,
    ⟨[1441, 15], [1441], [
      .prior 4207 true [15],
      .prior 4203 true [15],
      .prior 869 true [11, 15],
      .prior 4208 true [15, 11, 15],
      .equation 136 false false
        [1441]
        [],
      .prior 4187 false []]⟩,
    ⟨[1441, 17], [1441], [
      .prior 4207 true [17],
      .prior 4203 true [17],
      .prior 879 true [11, 17],
      .prior 4208 true [17, 11, 17],
      .equation 44 false false
        [1441]
        [],
      .prior 4187 false []]⟩,
    ⟨[1441, 5], [1439], [
      .prior 4186 false []]⟩,
    ⟨[1439, 1], [1439, 1], [
]⟩,
    ⟨[1439, 1], [1439], [
      .prior 4214 false [],
      .prior 4213 true [1],
      .equation 26 false false
        [1441, 0]
        [4],
      .equation 2 true false
        [1441, 0]
        [4],
      .equation 758 true false
        []
        [4],
      .prior 4207 false [4],
      .equation 6 true false
        [1441, 4]
        [],
      .prior 4186 false [],
      .prior 4185 false []]⟩,
    ⟨[1437, 5], [1437, 5], [
]⟩,
    ⟨[1437, 5], [1437], [
      .prior 4216 false [],
      .prior 4184 true [5],
      .prior 4213 true [3, 5],
      .equation 33 false false
        [1441, 2]
        [4, 2],
      .equation 4 true false
        [1441, 2]
        [4, 2],
      .prior 4209 false [4, 2],
      .equation 6 true false
        [1441, 4]
        [2],
      .prior 4186 false [2],
      .equation 4 true false
        [1439, 2]
        [],
      .prior 4184 false [],
      .prior 4183 false []]⟩,
    ⟨[1439, 15], [1439, 15], [
]⟩,
    ⟨[1439, 15], [1439], [
      .prior 4218 false [],
      .prior 4213 true [15],
      .equation 30 false false
        [1441]
        [14, 4],
      .equation 12 true false
        [1441, 14]
        [4],
      .prior 4211 false [4],
      .equation 6 true false
        [1441, 4]
        [],
      .prior 4186 false [],
      .prior 4185 false []]⟩,
    ⟨[1439, 17], [1439, 17], [
]⟩,
    ⟨[1439, 17], [1439], [
      .prior 4220 false [],
      .prior 4213 true [17],
      .equation 31 false false
        [1441]
        [16, 4],
      .equation 14 true false
        [1441, 16]
        [4],
      .prior 4212 false [4],
      .equation 6 true false
        [1441, 4]
        [],
      .prior 4186 false [],
      .prior 4185 false []]⟩,
    ⟨[1439, 2], [1437], [
      .equation 4 true false
        [1439, 2]
        [],
      .prior 4184 false []]⟩,
    ⟨[1435, 3], [1435, 3], [
]⟩]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
