/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal acyclic path parents and exact source-generator bounds in this finite interval. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact raw parent and generator indices, before any finite generator decoding. -/
def y422TPathRawData11 : Fin 128 → ℕ × ℕ :=
  ![(1407, 0),
    (1408, 7),
    (1409, 8),
    (1410, 0),
    (1411, 1),
    (1412, 2),
    (1413, 0),
    (1414, 5),
    (1415, 6),
    (71, 8),
    (401, 8),
    (909, 7),
    (1132, 7),
    (1420, 0),
    (1421, 1),
    (1422, 2),
    (1423, 5),
    (1424, 6),
    (1425, 0),
    (1426, 7),
    (1427, 8),
    (1428, 0),
    (1429, 1),
    (1430, 2),
    (1431, 0),
    (1432, 5),
    (1433, 6),
    (1434, 0),
    (1435, 7),
    (1436, 8),
    (1437, 0),
    (1438, 1),
    (1439, 2),
    (1440, 0),
    (1441, 5),
    (1442, 6),
    (1443, 0),
    (1444, 7),
    (1445, 8),
    (1446, 0),
    (1447, 1),
    (1448, 2),
    (1449, 0),
    (1450, 5),
    (1451, 6),
    (1452, 0),
    (1453, 7),
    (1454, 8),
    (1455, 0),
    (1456, 1),
    (1457, 2),
    (1458, 0),
    (1459, 5),
    (1460, 6),
    (1461, 0),
    (1462, 7),
    (1463, 8),
    (1464, 0),
    (1465, 1),
    (1466, 2),
    (1467, 0),
    (1468, 5),
    (1469, 6),
    (1470, 0),
    (1471, 7),
    (1472, 8),
    (1473, 0),
    (1474, 1),
    (1475, 2),
    (1476, 0),
    (1477, 5),
    (1478, 6),
    (1479, 0),
    (1480, 7),
    (1481, 8),
    (1482, 0),
    (1483, 1),
    (1484, 2),
    (1485, 0),
    (1486, 5),
    (1487, 6),
    (280, 8),
    (910, 7),
    (497, 8),
    (912, 0),
    (1492, 1),
    (1493, 2),
    (1494, 5),
    (1495, 6),
    (1496, 0),
    (1497, 7),
    (1498, 8),
    (1499, 0),
    (1500, 1),
    (1501, 2),
    (1502, 0),
    (1503, 5),
    (1504, 6),
    (1505, 0),
    (1506, 7),
    (1507, 8),
    (1508, 0),
    (1509, 1),
    (1510, 2),
    (1511, 0),
    (1512, 5),
    (1513, 6),
    (1514, 0),
    (1515, 7),
    (1516, 8),
    (1517, 0),
    (1518, 1),
    (1519, 2),
    (1520, 0),
    (1521, 5),
    (1522, 6),
    (1523, 0),
    (1524, 7),
    (1525, 8),
    (1526, 0),
    (1527, 1),
    (1528, 2),
    (1529, 0),
    (1530, 5),
    (1531, 6),
    (1532, 0),
    (1533, 7),
    (1534, 8)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData11_allowed (j : Fin 128) :
    (1408 + j.val = 0 ∨ (y422TPathRawData11 j).1 < 1408 + j.val) ∧
      (y422TPathRawData11 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
