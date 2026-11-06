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
def y422TPathRawData12 : Fin 128 → ℕ × ℕ :=
  ![(1535, 0),
    (1536, 1),
    (1537, 2),
    (1538, 0),
    (1539, 5),
    (1540, 6),
    (1541, 0),
    (1542, 7),
    (1543, 8),
    (1544, 0),
    (1545, 1),
    (1546, 2),
    (1547, 0),
    (1548, 5),
    (1549, 6),
    (1550, 0),
    (1551, 7),
    (1552, 8),
    (1553, 0),
    (281, 8),
    (32, 8),
    (988, 0),
    (1557, 1),
    (1558, 2),
    (1559, 5),
    (1560, 6),
    (1561, 0),
    (1562, 7),
    (1563, 8),
    (1564, 1),
    (1565, 2),
    (1566, 0),
    (1567, 5),
    (1568, 6),
    (1569, 0),
    (1570, 7),
    (1571, 8),
    (1572, 0),
    (1573, 1),
    (1574, 2),
    (1575, 0),
    (1576, 5),
    (1577, 6),
    (1578, 0),
    (1579, 7),
    (1580, 8),
    (1581, 0),
    (1582, 1),
    (1583, 2),
    (1584, 0),
    (1585, 5),
    (1586, 6),
    (1587, 0),
    (1588, 7),
    (1589, 8),
    (1590, 0),
    (1591, 1),
    (1592, 2),
    (1593, 0),
    (1594, 5),
    (1595, 6),
    (1596, 0),
    (1597, 7),
    (1598, 8),
    (1599, 0),
    (1600, 1),
    (1601, 2),
    (1602, 0),
    (1603, 5),
    (1604, 6),
    (1605, 0),
    (1606, 7),
    (1607, 8),
    (1608, 0),
    (1609, 1),
    (1610, 2),
    (1611, 0),
    (1612, 5),
    (1613, 6),
    (1614, 0),
    (1615, 7),
    (1616, 8),
    (1617, 0),
    (1618, 1),
    (1619, 2),
    (1620, 0),
    (1621, 5),
    (192, 8),
    (1206, 7),
    (1624, 8),
    (1415, 1),
    (1626, 2),
    (1627, 0),
    (1628, 5),
    (1629, 6),
    (1630, 0),
    (1631, 7),
    (1632, 8),
    (1633, 0),
    (1634, 1),
    (1635, 2),
    (1636, 0),
    (1637, 5),
    (1638, 6),
    (1639, 0),
    (1640, 7),
    (1641, 8),
    (1642, 0),
    (1643, 1),
    (1644, 2),
    (1645, 0),
    (1646, 5),
    (1647, 6),
    (1648, 0),
    (1649, 7),
    (1650, 8),
    (1651, 0),
    (1652, 1),
    (1653, 2),
    (1654, 0),
    (1655, 5),
    (1656, 6),
    (1657, 0),
    (1658, 7),
    (1659, 8),
    (1660, 0),
    (1661, 1),
    (1662, 2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData12_allowed (j : Fin 128) :
    (1536 + j.val = 0 ∨ (y422TPathRawData12 j).1 < 1536 + j.val) ∧
      (y422TPathRawData12 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
