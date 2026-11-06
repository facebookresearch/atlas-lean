/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal chronological equation data for the original-source C431 replay, block 13. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawContextPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Exact raw source or earlier-equation contextual derivations, chronological block 13. -/
def y431AuxReplayData13 : Fin 128 → Y322RawContextCertificate :=
![
  ⟨[1321, 11], [175, 1321], .contexts [⟨1661, false, false, [], []⟩, ⟨1662, false, false, [],
    []⟩, ⟨1663, false, false, [], []⟩, ⟨1663, false, false, [], []⟩]⟩
,
  ⟨[1321, 5], [1319], .contexts [⟨1532, false, false, [], []⟩]⟩
,
  ⟨[1321, 5], [1319], .contexts [⟨1665, false, false, [], []⟩, ⟨1503, false, false, [], []⟩,
    ⟨1504, false, false, [], []⟩, ⟨1504, false, false, [], []⟩]⟩
,
  ⟨[174], [174], .contexts []⟩
,
  ⟨[1321, 13], [153, 1321], .contexts [⟨1510, false, false, [], []⟩, ⟨1658, false, false, [],
    []⟩, ⟨1650, false, false, [], []⟩, ⟨1650, false, false, [], []⟩]⟩
,
  ⟨[153, 1321, 5], [153, 1319], .contexts [⟨1506, false, false, [153], []⟩]⟩
,
  ⟨[181, 1321], [181, 1321], .contexts []⟩
,
  ⟨[1321, 15], [181, 1321], .contexts [⟨1660, false, false, [], []⟩, ⟨1660, false, false, [],
    []⟩, ⟨165, false, false, [176], [1321, 15]⟩, ⟨1657, true, false, [176], [15]⟩, ⟨1659, false,
    false, [176, 1325], []⟩, ⟨1644, false, false, [176], []⟩, ⟨1641, false, false, [176], []⟩,
    ⟨1658, false, false, [176], []⟩, ⟨1650, false, false, [176], []⟩, ⟨1650, false, false,
    [176], []⟩, ⟨1509, false, false, [176, 153], []⟩, ⟨166, true, false, [], [153, 1321]⟩, ⟨167,
    true, false, [], [1321]⟩, ⟨1670, false, false, [], []⟩, ⟨1670, false, false, [], []⟩]⟩
,
  ⟨[181], [181], .contexts [⟨877, false, false, [], [181]⟩]⟩
,
  ⟨[185], [185], .contexts []⟩
,
  ⟨[185], [185], .contexts []⟩
,
  ⟨[185], [185], .contexts []⟩
,
  ⟨[1319], [185, 1317], .contexts [⟨1666, true, false, [], []⟩, ⟨1672, false, false, [180],
    [1321, 5]⟩, ⟨1509, true, false, [], [5]⟩, ⟨1671, true, false, [180], [5]⟩, ⟨872, true,
    false, [180, 1321], [5]⟩, ⟨1329, true, false, [180, 1321], [14, 5]⟩, ⟨1666, false, false,
    [180], [15, 5, 5]⟩, ⟨1534, false, false, [180], [5, 5]⟩, ⟨1500, false, false, [180], [5,
    5]⟩, ⟨1501, false, false, [180], [5, 5]⟩, ⟨1501, false, false, [180], [5, 5]⟩, ⟨8, false,
    false, [180, 1317], []⟩, ⟨169, true, false, [], [1317]⟩, ⟨1675, true, false, [], [1317]⟩,
    ⟨1674, true, false, [], [1317]⟩, ⟨1673, true, false, [], [1317]⟩]⟩
,
  ⟨[185, 1317], [185, 1317], .contexts []⟩
,
  ⟨[1319], [185, 1317], .contexts [⟨1676, false, false, [], []⟩, ⟨1677, false, false, [], []⟩]⟩
,
  ⟨[181], [184], .contexts [⟨169, true, true, [], []⟩]⟩
,
  ⟨[153, 1319], [153, 185, 1317], .contexts [⟨1678, false, false, [153], []⟩]⟩
,
  ⟨[189, 1317], [189, 1317], .contexts []⟩
,
  ⟨[1317, 11, 1], [189, 1317, 1], .contexts [⟨1676, true, false, [184], [11, 1]⟩, ⟨1506, true,
    false, [184], [11, 1]⟩, ⟨1664, true, false, [184, 174], [5, 11, 1]⟩, ⟨1109, false, false,
    [184, 174, 1321], [4, 1]⟩, ⟨900, false, false, [184, 174, 1321], [1]⟩, ⟨1666, false, false,
    [184, 174], [1]⟩, ⟨1505, false, false, [184, 174], [1]⟩, ⟨1667, true, false, [184], [1319,
    1]⟩, ⟨1667, true, false, [184], [1319, 1]⟩, ⟨168, true, false, [184], [1319, 1]⟩, ⟨1678,
    false, false, [184, 183], [1]⟩, ⟨1679, true, false, [], [183, 185, 1317, 1]⟩, ⟨170, true,
    false, [], [185, 1317, 1]⟩, ⟨171, true, false, [], [1317, 1]⟩, ⟨1681, false, false, [],
    [1]⟩, ⟨1681, false, false, [], [1]⟩]⟩
,
  ⟨[1317, 1], [1315], .contexts [⟨1535, false, false, [], []⟩, ⟨1495, false, false, [], []⟩,
    ⟨1496, false, false, [], []⟩, ⟨1496, false, false, [], []⟩]⟩
,
  ⟨[11, 1, 11, 1, 11, 1], [], .contexts [⟨50, false, false, [0], [1]⟩]⟩
,
  ⟨[0, 10], [1, 11], .contexts [⟨871, false, false, [], [10]⟩, ⟨926, false, false, [1], []⟩]⟩
,
  ⟨[188], [188], .contexts []⟩
,
  ⟨[193, 1317], [193, 1317], .contexts []⟩
,
  ⟨[1317, 13, 1], [193, 1315], .contexts [⟨1676, true, false, [184], [13, 1]⟩, ⟨1666, true,
    false, [184], [13, 1]⟩, ⟨1321, false, false, [184, 1321], [1]⟩, ⟨1322, false, false, [184,
    1321], [1]⟩, ⟨1668, false, false, [184], [5, 1]⟩, ⟨1669, false, false, [184], [1]⟩, ⟨1505,
    false, false, [184, 153], [1]⟩, ⟨1635, true, false, [184], [1319, 1]⟩, ⟨1680, false, false,
    [184], [1]⟩, ⟨1679, true, false, [], [153, 185, 1317, 1]⟩, ⟨172, true, false, [], [185,
    1317, 1]⟩, ⟨173, true, false, [], [1317, 1]⟩, ⟨1687, false, false, [], [1]⟩, ⟨1687, false,
    false, [], [1]⟩, ⟨1499, false, false, [193], []⟩]⟩
,
  ⟨[13, 1, 13], [0], .contexts [⟨949, false, false, [], [0]⟩]⟩
,
  ⟨[1315, 13], [1315, 13], .contexts []⟩
,
  ⟨[192], [192], .contexts []⟩
,
  ⟨[1315, 13], [197, 1315], .contexts [⟨1690, false, false, [], []⟩, ⟨1688, true, false, [192],
    [13]⟩, ⟨1689, false, false, [192, 1317], []⟩, ⟨871, false, false, [192, 1317], []⟩, ⟨1683,
    false, false, [192], []⟩, ⟨1497, false, false, [192], []⟩, ⟨1691, true, false, [], [1315]⟩,
    ⟨1691, true, false, [], [1315]⟩, ⟨175, true, false, [], [1315]⟩]⟩
,
  ⟨[1319], [185, 1317], .contexts [⟨1678, false, false, [], []⟩]⟩
,
  ⟨[185, 1317, 1], [185, 1315], .contexts [⟨1499, false, false, [185], []⟩]⟩
,
  ⟨[185, 1315], [185, 1315], .contexts []⟩
,
  ⟨[185, 1315], [185, 1315], .contexts []⟩
,
  ⟨[185, 1315], [185, 1315], .contexts []⟩
,
  ⟨[1315, 15], [1315, 15], .contexts []⟩
,
  ⟨[185, 1315], [185, 1315], .contexts [⟨1497, false, false, [185], []⟩]⟩
,
  ⟨[185], [185], .contexts [⟨877, false, false, [], [185]⟩, ⟨1674, false, false, [], []⟩, ⟨1675,
    false, false, [], []⟩]⟩
,
  ⟨[185, 1315], [185, 1315], .contexts [⟨1700, true, false, [], [1315]⟩]⟩
,
  ⟨[1315, 15], [185, 1315], .contexts [⟨1698, false, false, [], []⟩, ⟨1683, true, false, [],
    [15]⟩, ⟨1188, false, false, [1317], []⟩, ⟨1189, false, false, [1317], []⟩, ⟨1502, false,
    false, [], [1]⟩, ⟨1693, false, false, [], [1]⟩, ⟨1677, false, false, [], [1]⟩, ⟨1677, false,
    false, [], [1]⟩, ⟨1694, false, false, [], []⟩, ⟨1695, false, false, [], []⟩, ⟨1696, false,
    false, [], []⟩, ⟨1697, false, false, [], []⟩, ⟨1699, false, false, [], []⟩, ⟨1701, false,
    false, [], []⟩]⟩
,
  ⟨[185, 1315, 11], [185, 1313], .contexts [⟨1494, false, false, [185], []⟩]⟩
,
  ⟨[185, 1313], [185, 1313], .contexts []⟩
,
  ⟨[185, 1313], [185, 1313], .contexts []⟩
,
  ⟨[185, 1313], [185, 1313], .contexts []⟩
,
  ⟨[1315, 11], [1313], .contexts [⟨1536, false, false, [], []⟩, ⟨1491, false, false, [], []⟩,
    ⟨1492, false, false, [], []⟩, ⟨1492, false, false, [], []⟩]⟩
,
  ⟨[1315, 10], [1315, 11], .contexts [⟨926, false, false, [1315], []⟩]⟩
,
  ⟨[1313, 15], [1313, 15], .contexts []⟩
,
  ⟨[181], [184], .contexts [⟨1679, false, false, [], []⟩]⟩
,
  ⟨[184], [184], .contexts []⟩
,
  ⟨[181], [184], .contexts [⟨1710, false, false, [], []⟩, ⟨1711, false, false, [], []⟩, ⟨1711,
    false, false, [], []⟩]⟩
,
  ⟨[181, 1313], [181, 1313], .contexts []⟩
,
  ⟨[1313, 15], [181, 1313], .contexts [⟨1709, false, false, [], []⟩, ⟨1709, false, false, [],
    []⟩, ⟨1706, true, false, [184], [15]⟩, ⟨1705, true, false, [184], [15]⟩, ⟨1704, true, false,
    [184], [15]⟩, ⟨1703, true, false, [184], [15]⟩, ⟨1697, true, false, [184], [11, 15]⟩, ⟨1697,
    true, false, [184], [11, 15]⟩, ⟨1695, true, false, [184], [11, 15]⟩, ⟨1702, true, false,
    [184], [11, 15]⟩, ⟨1698, true, false, [184], [11, 15]⟩, ⟨924, false, false, [184, 1315],
    [10]⟩, ⟨1708, false, false, [184], []⟩, ⟨1707, false, false, [184], []⟩, ⟨1493, false,
    false, [184], []⟩, ⟨1712, true, false, [], [1313]⟩, ⟨1713, false, false, [], []⟩, ⟨1713,
    false, false, [], []⟩]⟩
,
  ⟨[1313, 3], [1311], .contexts [⟨1537, false, false, [], []⟩]⟩
,
  ⟨[1313, 3], [1311], .contexts [⟨1715, false, false, [], []⟩, ⟨1488, false, false, [], []⟩,
    ⟨1489, false, false, [], []⟩, ⟨1489, false, false, [], []⟩]⟩
,
  ⟨[1311, 15], [1311, 15], .contexts []⟩
,
  ⟨[180], [180], .contexts []⟩
,
  ⟨[185, 1311], [185, 1311], .contexts []⟩
,
  ⟨[1311, 15, 17], [185, 1309], .contexts [⟨1717, false, false, [], [17]⟩, ⟨1717, false, false,
    [], [17]⟩, ⟨1490, true, false, [], [15, 17]⟩, ⟨1714, true, false, [180], [3, 15, 17]⟩, ⟨886,
    false, false, [180, 1313], [2, 17]⟩, ⟨888, false, false, [180, 1313], [17]⟩, ⟨1716, false,
    false, [180], [17]⟩, ⟨1718, true, false, [], [1311, 17]⟩, ⟨1718, true, false, [], [1311,
    17]⟩, ⟨169, true, false, [], [1311, 17]⟩, ⟨1673, true, false, [], [1311, 17]⟩, ⟨1719, false,
    false, [], [17]⟩, ⟨1719, false, false, [], [17]⟩, ⟨1487, false, false, [185], []⟩]⟩
,
  ⟨[1309, 15], [1309, 15], .contexts []⟩
,
  ⟨[1309, 15], [181, 1309], .contexts [⟨1721, false, false, [], []⟩, ⟨1720, true, false, [184],
    [15]⟩, ⟨1659, false, false, [184, 1311], []⟩, ⟨938, false, false, [184, 1311], []⟩, ⟨1538,
    false, false, [184], []⟩, ⟨1479, false, false, [184], []⟩, ⟨1480, false, false, [184], []⟩,
    ⟨1480, false, false, [184], []⟩, ⟨1485, false, false, [184], []⟩, ⟨1712, true, false, [],
    [1309]⟩]⟩
,
  ⟨[1327, 17], [1333], .contexts [⟨176, true, false, [], []⟩]⟩
,
  ⟨[1333, 17], [1327], .contexts [⟨1723, true, false, [], [17]⟩, ⟨16, false, false, [1327], []⟩,
    ⟨1520, false, false, [], []⟩]⟩
,
  ⟨[1333], [1333], .contexts []⟩
,
  ⟨[1327, 17], [1333], .contexts [⟨1723, false, false, [], []⟩, ⟨1725, false, false, [], []⟩,
    ⟨1725, false, false, [], []⟩]⟩
,
  ⟨[137, 1331], [137, 1331], .contexts []⟩
,
  ⟨[1333], [1333], .contexts []⟩
,
  ⟨[1333, 1], [201, 1333], .contexts [⟨1726, true, false, [], [1]⟩, ⟨1200, false, false, [1327],
    []⟩, ⟨1201, false, false, [1327], []⟩, ⟨1605, false, false, [], [17, 1, 17]⟩, ⟨1727, false,
    false, [], [17, 1, 17]⟩, ⟨1727, false, false, [], [17, 1, 17]⟩, ⟨1595, false, false, [137],
    [1, 17]⟩, ⟨177, true, false, [], [1331, 1, 17]⟩, ⟨1526, false, false, [199], [17]⟩, ⟨1602,
    false, false, [199], [17]⟩, ⟨178, true, false, [], [1327, 17]⟩, ⟨1723, false, false, [201],
    []⟩, ⟨1728, false, false, [201], []⟩]⟩
,
  ⟨[17, 3, 17, 3], [], .contexts [⟨179, false, false, [2], [3]⟩]⟩
,
  ⟨[17, 3], [2, 16], .contexts [⟨1730, false, false, [], [2, 16]⟩]⟩
,
  ⟨[2, 16], [3, 17], .contexts [⟨888, false, false, [], [16]⟩, ⟨938, false, false, [3], []⟩]⟩
,
  ⟨[1333, 3], [1333, 3], .contexts []⟩
,
  ⟨[1333, 3], [153, 1321], .contexts [⟨1733, false, false, [], []⟩, ⟨1726, true, false, [],
    [3]⟩, ⟨1731, false, false, [1327], []⟩, ⟨1732, false, false, [1327], []⟩, ⟨1624, false,
    false, [], [17]⟩, ⟨1531, false, false, [], []⟩, ⟨1658, false, false, [], []⟩, ⟨1650, false,
    false, [], []⟩, ⟨1650, false, false, [], []⟩, ⟨1509, false, false, [153], []⟩, ⟨1635, true,
    false, [], [1321]⟩]⟩
,
  ⟨[1321, 3], [167, 1333], .contexts [⟨1734, true, false, [152], [3]⟩, ⟨6, false, false, [152,
    1333], []⟩, ⟨160, true, false, [], [1333]⟩]⟩
,
  ⟨[141, 1327], [141, 1327], .contexts []⟩
,
  ⟨[141, 1333], [141, 1333], .contexts []⟩
,
  ⟨[141, 1333], [141, 1333], .contexts []⟩
,
  ⟨[1333, 5], [1333, 5], .contexts []⟩
,
  ⟨[17, 19, 17, 19], [], .contexts [⟨35, false, false, [18], [19]⟩]⟩
,
  ⟨[1333, 5, 3], [141, 153, 1321], .contexts [⟨1739, false, false, [], [3]⟩, ⟨1739, false,
    false, [], [3]⟩, ⟨1726, true, false, [], [5, 3]⟩, ⟨1208, false, false, [1327], [3]⟩, ⟨1209,
    false, false, [1327], [3]⟩, ⟨1606, false, false, [], [17, 3]⟩, ⟨1736, false, false, [], [17,
    3]⟩, ⟨1736, false, false, [], [17, 3]⟩, ⟨1723, false, false, [141], [3]⟩, ⟨1737, false,
    false, [], [3]⟩, ⟨1738, false, false, [], [3]⟩, ⟨1728, false, false, [141], [3]⟩, ⟨877,
    true, false, [], [141, 1333, 3]⟩, ⟨1737, false, false, [], [3]⟩, ⟨1738, false, false, [],
    [3]⟩, ⟨1738, false, false, [], [3]⟩, ⟨1734, false, false, [141], []⟩]⟩
,
  ⟨[3, 5, 3, 5, 3, 5], [], .contexts [⟨183, false, false, [], []⟩]⟩
,
  ⟨[4, 2, 4], [5, 3, 5], .contexts [⟨900, false, false, [], [2, 4]⟩, ⟨888, false, false, [5],
    [4]⟩, ⟨900, false, false, [5, 3], []⟩]⟩
,
  ⟨[3, 19], [18, 2], .contexts [⟨29, false, false, [18], [2]⟩]⟩
,
  ⟨[18, 2], [19, 3], .contexts [⟨984, false, false, [], [2]⟩, ⟨888, false, false, [19], []⟩]⟩
,
  ⟨[1321, 1], [1335], .contexts [⟨186, true, false, [], []⟩]⟩
,
  ⟨[1335, 1], [1321], .contexts [⟨1746, true, false, [], [1]⟩, ⟨4, false, false, [1321], []⟩,
    ⟨1508, false, false, [], []⟩]⟩
,
  ⟨[1335], [1335], .contexts []⟩
,
  ⟨[1321, 1], [1335], .contexts [⟨1746, false, false, [], []⟩, ⟨1748, false, false, [], []⟩,
    ⟨1748, false, false, [], []⟩]⟩
,
  ⟨[167, 1333], [167, 1333], .contexts []⟩
,
  ⟨[1335, 3], [215, 1335], .contexts [⟨1749, true, false, [], [3]⟩, ⟨1288, false, false, [1321],
    []⟩, ⟨1289, false, false, [1321], []⟩, ⟨1735, false, false, [], [1, 3, 1]⟩, ⟨1750, false,
    false, [], [1, 3, 1]⟩, ⟨1750, false, false, [], [1, 3, 1]⟩, ⟨1729, false, false, [167], [3,
    1]⟩, ⟨877, true, false, [167], [201, 1333, 3, 1]⟩, ⟨187, true, false, [], [1333, 3, 1]⟩,
    ⟨1734, false, false, [213], [1]⟩, ⟨188, true, false, [], [1321, 1]⟩, ⟨1746, false, false,
    [215], []⟩]⟩
,
  ⟨[1335], [1335], .contexts []⟩
,
  ⟨[1335, 3], [215, 1335], .contexts [⟨1751, false, false, [], []⟩, ⟨1752, false, false, [215],
    []⟩, ⟨877, true, false, [], [215, 1335]⟩]⟩
,
  ⟨[1335, 5], [1335, 5], .contexts []⟩
,
  ⟨[1335, 5], [185, 1315], .contexts [⟨1754, false, false, [], []⟩, ⟨1749, true, false, [],
    [5]⟩, ⟨1153, false, false, [1321], []⟩, ⟨1154, false, false, [1321], []⟩, ⟨1665, false,
    false, [], [1]⟩, ⟨1693, false, false, [], [1]⟩, ⟨1677, false, false, [], [1]⟩, ⟨1677, false,
    false, [], [1]⟩, ⟨1694, false, false, [], []⟩, ⟨1695, false, false, [], []⟩, ⟨1696, false,
    false, [], []⟩, ⟨1697, false, false, [], []⟩, ⟨1699, false, false, [], []⟩, ⟨1701, false,
    false, [], []⟩]⟩
,
  ⟨[1315, 5], [181, 1335], .contexts [⟨1755, true, false, [184], [5]⟩, ⟨8, false, false, [184,
    1335], []⟩, ⟨1679, true, false, [], [1335]⟩]⟩
,
  ⟨[171, 1321], [171, 1321], .contexts []⟩
,
  ⟨[171, 1335], [171, 1335], .contexts []⟩
,
  ⟨[1321, 7, 1], [171, 1335], .contexts [⟨1654, true, false, [152], [7, 1]⟩, ⟨1645, false,
    false, [152, 164], [1]⟩, ⟨1642, false, false, [152, 164], [1]⟩, ⟨1514, false, false, [152,
    164], [1]⟩, ⟨1646, true, false, [152], [1323, 1]⟩, ⟨1646, true, false, [152], [1323, 1]⟩,
    ⟨159, false, true, [152], [1323, 1]⟩, ⟨1655, false, false, [152, 145], [1]⟩, ⟨160, true,
    false, [], [145, 153, 1321, 1]⟩, ⟨161, true, false, [], [153, 1321, 1]⟩, ⟨162, true, false,
    [], [1321, 1]⟩, ⟨1757, false, false, [], [1]⟩, ⟨1757, false, false, [], [1]⟩, ⟨1746, false,
    false, [171], []⟩, ⟨1758, false, false, [], []⟩]⟩
,
  ⟨[171, 1335], [171, 1335], .contexts []⟩
,
  ⟨[1335, 7], [1335, 7], .contexts []⟩
,
  ⟨[171], [171], .contexts [⟨877, false, false, [], [171]⟩]⟩
,
  ⟨[181, 1335], [181, 1335], .contexts []⟩
,
  ⟨[181, 1335], [181, 1335], .contexts []⟩
,
  ⟨[1335, 15], [1335, 15], .contexts []⟩
,
  ⟨[1335, 15], [181, 1335], .contexts [⟨1765, false, false, [], []⟩, ⟨1749, true, false, [],
    [15]⟩, ⟨1188, false, false, [1321], []⟩, ⟨1189, false, false, [1321], []⟩, ⟨1671, false,
    false, [], [1]⟩, ⟨1746, false, false, [181], []⟩, ⟨1763, false, false, [], []⟩, ⟨1764,
    false, false, [], []⟩, ⟨1752, false, false, [181], []⟩, ⟨1672, true, false, [], [1335]⟩]⟩
,
  ⟨[167, 1325], [167, 1325], .contexts []⟩
,
  ⟨[219, 1335], [219, 1335], .contexts []⟩
,
  ⟨[219, 1335], [219, 1335], .contexts []⟩
,
  ⟨[1, 17], [16, 0, 16, 0], .contexts [⟨52, false, false, [], [16, 0, 16, 0]⟩]⟩
,
  ⟨[16, 0, 16, 0], [17, 1, 17, 1], .contexts [⟨938, false, false, [], [0, 16, 0]⟩, ⟨871, false,
    false, [17], [16, 0]⟩, ⟨938, false, false, [17, 1], [0]⟩, ⟨871, false, false, [17, 1, 17],
    []⟩]⟩
,
  ⟨[1335, 17], [1335, 17], .contexts []⟩
,
  ⟨[1335, 17], [219, 1335], .contexts [⟨1772, false, false, [], []⟩, ⟨1749, true, false, [],
    [17]⟩, ⟨1770, false, false, [1321], []⟩, ⟨1771, false, false, [1321], []⟩, ⟨1651, false,
    false, [], [1, 17, 1]⟩, ⟨1653, false, false, [], [1, 17, 1]⟩, ⟨1767, false, false, [], [1,
    17, 1]⟩, ⟨1767, false, false, [], [1, 17, 1]⟩, ⟨1621, false, false, [167], [17, 1]⟩, ⟨189,
    true, false, [], [1325, 17, 1]⟩, ⟨1515, false, false, [217], [1]⟩, ⟨1655, false, false,
    [217], [1]⟩, ⟨190, true, false, [], [1321, 1]⟩, ⟨1746, false, false, [219], []⟩, ⟨1768,
    false, false, [], []⟩, ⟨1769, false, false, [], []⟩, ⟨1752, false, false, [219], []⟩]⟩
,
  ⟨[1335, 17], [219, 1335], .contexts [⟨1773, false, false, [], []⟩, ⟨877, true, false, [],
    [219, 1335]⟩]⟩
,
  ⟨[1321, 11, 3, 17, 13, 5, 15], [227, 1327], .contexts [⟨1664, false, false, [], [3, 17, 13, 5,
    15]⟩, ⟨1735, false, false, [175], [17, 13, 5, 15]⟩, ⟨191, true, false, [], [1333, 17, 13, 5,
    15]⟩, ⟨1724, false, false, [221], [13, 5, 15]⟩, ⟨1610, false, false, [221], [5, 15]⟩, ⟨192,
    true, false, [], [1327, 5, 15]⟩, ⟨1606, false, false, [223], [15]⟩, ⟨193, true, false, [],
    [1327, 15]⟩, ⟨1612, false, false, [225], []⟩, ⟨194, true, false, [], [1327]⟩]⟩
,
  ⟨[1321, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13], [235, 1263], .contexts [⟨1775, false, false,
    [], [1, 11, 3, 17, 13]⟩, ⟨1605, false, false, [227], [11, 3, 17, 13]⟩, ⟨195, true, false,
    [], [1331, 11, 3, 17, 13]⟩, ⟨1585, false, false, [229], [3, 17, 13]⟩, ⟨196, true, false, [],
    [1265, 3, 17, 13]⟩, ⟨957, false, false, [231], [17, 13]⟩, ⟨98, true, false, [231], [1265,
    17, 13]⟩, ⟨197, true, false, [], [1265, 17, 13]⟩, ⟨977, false, false, [233], [13]⟩, ⟨100,
    true, false, [233], [1265, 13]⟩, ⟨198, true, false, [], [1265, 13]⟩, ⟨944, false, false,
    [235], []⟩]⟩
,
  ⟨[1321, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3], [243], .contexts [⟨1776,
    false, false, [], [5, 15, 1, 11, 3]⟩, ⟨904, false, false, [235], [15, 1, 11, 3]⟩, ⟨95, true,
    false, [235], [1263, 15, 1, 11, 3]⟩, ⟨199, true, false, [], [1263, 15, 1, 11, 3]⟩, ⟨858,
    false, false, [237], [1, 11, 3]⟩, ⟨92, true, false, [237], [11, 3]⟩, ⟨200, true, false, [],
    [11, 3]⟩, ⟨89, true, false, [239], [3]⟩, ⟨201, true, false, [], [3]⟩, ⟨98, true, false,
    [241], []⟩, ⟨202, true, false, [], []⟩]⟩
,
  ⟨[1321, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1], [251,
    1263], .contexts [⟨1777, false, false, [], [17, 13, 5, 15, 1]⟩, ⟨100, true, false, [243],
    [13, 5, 15, 1]⟩, ⟨203, true, false, [], [13, 5, 15, 1]⟩, ⟨88, true, false, [245], [5, 15,
    1]⟩, ⟨204, true, false, [], [5, 15, 1]⟩, ⟨95, true, false, [247], [15, 1]⟩, ⟨205, true,
    false, [], [15, 1]⟩, ⟨856, false, false, [249], [1]⟩, ⟨879, false, false, [249], []⟩, ⟨92,
    true, false, [249], [1263]⟩, ⟨206, true, false, [], [1263]⟩]⟩
,
  ⟨[1321, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5], [259, 1265], .contexts [⟨1778, false, false, [], [11, 3, 17, 13, 5]⟩, ⟨929, false,
    false, [251], [3, 17, 13, 5]⟩, ⟨89, true, false, [251], [1263, 3, 17, 13, 5]⟩, ⟨207, true,
    false, [], [1263, 3, 17, 13, 5]⟩, ⟨892, false, false, [253], [17, 13, 5]⟩, ⟨98, true, false,
    [253], [1263, 17, 13, 5]⟩, ⟨208, true, false, [], [1263, 17, 13, 5]⟩, ⟨942, false, false,
    [255], [13, 5]⟩, ⟨100, true, false, [255], [1263, 13, 5]⟩, ⟨209, true, false, [], [1263, 13,
    5]⟩, ⟨943, false, false, [257], [5]⟩, ⟨960, false, false, [257], []⟩, ⟨95, true, false,
    [257], [1265]⟩, ⟨210, true, false, [], [1265]⟩]⟩
,
  ⟨[1321, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5, 15, 1, 11, 3, 17], [269, 1331], .contexts [⟨1779, false, false, [], [15, 1, 11, 3,
    17]⟩, ⟨973, false, false, [259], [1, 11, 3, 17]⟩, ⟨88, true, false, [259], [1265, 1, 11, 3,
    17]⟩, ⟨211, true, false, [], [1265, 1, 11, 3, 17]⟩, ⟨954, false, false, [261], [11, 3, 17]⟩,
    ⟨92, true, false, [261], [1265, 11, 3, 17]⟩, ⟨212, true, false, [], [1265, 11, 3, 17]⟩,
    ⟨1584, false, false, [263], [3, 17]⟩, ⟨213, true, false, [], [1331, 3, 17]⟩, ⟨1580, false,
    false, [265], [17]⟩, ⟨214, true, false, [], [1331, 17]⟩, ⟨1595, false, false, [267], []⟩,
    ⟨215, true, false, [], [1331]⟩]⟩
,
  ⟨[1321, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11], [279, 1327], .contexts [⟨1780, false, false, [],
    [13, 5, 15, 1, 11]⟩, ⟨1588, false, false, [269], [5, 15, 1, 11]⟩, ⟨216, true, false, [],
    [1331, 5, 15, 1, 11]⟩, ⟨1582, false, false, [271], [15, 1, 11]⟩, ⟨217, true, false, [],
    [1331, 15, 1, 11]⟩, ⟨1592, false, false, [273], [1, 11]⟩, ⟨218, true, false, [], [1331, 1,
    11]⟩, ⟨1526, false, false, [275], [11]⟩, ⟨1602, false, false, [275], [11]⟩, ⟨219, true,
    false, [], [1327, 11]⟩, ⟨1522, false, false, [277], []⟩, ⟨1602, false, false, [277], []⟩,
    ⟨220, true, false, [], [1327]⟩]⟩
,
  ⟨[1321, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15], [287, 1317], .contexts [⟨1781,
    false, false, [], [3, 17, 13, 5, 15]⟩, ⟨1519, false, false, [279], [17, 13, 5, 15]⟩, ⟨1515,
    false, false, [279], [13, 5, 15]⟩, ⟨1655, false, false, [279], [13, 5, 15]⟩, ⟨221, true,
    false, [], [1321, 13, 5, 15]⟩, ⟨1510, false, false, [281], [5, 15]⟩, ⟨1655, false, false,
    [281], [5, 15]⟩, ⟨222, true, false, [], [1321, 5, 15]⟩, ⟨1506, false, false, [283], [15]⟩,
    ⟨1678, false, false, [283], [15]⟩, ⟨223, true, false, [], [1317, 15]⟩, ⟨1502, false, false,
    [285], []⟩, ⟨1678, false, false, [285], []⟩, ⟨224, true, false, [], [1317]⟩]⟩
,
  ⟨[1321, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13], [287, 1307],
    .contexts [⟨1782, false, false, [], [1, 11, 3, 17, 13]⟩, ⟨1499, false, false, [287], [11, 3,
    17, 13]⟩, ⟨1494, false, false, [287], [3, 17, 13]⟩, ⟨1490, false, false, [287], [17, 13]⟩,
    ⟨1487, false, false, [287], [13]⟩, ⟨1478, false, false, [287], []⟩]⟩
,
  ⟨[1321, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11,
    3], [287, 1297], .contexts [⟨1783, false, false, [], [5, 15, 1, 11, 3]⟩, ⟨1468, false,
    false, [287], [15, 1, 11, 3]⟩, ⟨1459, false, false, [287], [1, 11, 3]⟩, ⟨1451, false, false,
    [287], [11, 3]⟩, ⟨1442, false, false, [287], [3]⟩, ⟨1432, false, false, [287], []⟩]⟩
,
  ⟨[1321, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11,
    3, 17, 13, 5, 15, 1], [289, 1289], .contexts [⟨1784, false, false, [], [17, 13, 5, 15, 1]⟩,
    ⟨1422, false, false, [287], [13, 5, 15, 1]⟩, ⟨1413, false, false, [287], [5, 15, 1]⟩, ⟨1403,
    false, false, [287], [15, 1]⟩, ⟨1401, false, false, [287], [1]⟩, ⟨88, true, false, [287],
    [1291, 1]⟩, ⟨225, true, false, [], [1291, 1]⟩, ⟨1387, false, false, [289], []⟩]⟩
,
  ⟨[1321, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11,
    3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5], [291, 1281], .contexts [⟨1785, false, false, [],
    [11, 3, 17, 13, 5]⟩, ⟨1371, false, false, [289], [3, 17, 13, 5]⟩, ⟨1352, false, false,
    [289], [17, 13, 5]⟩, ⟨1334, false, false, [289], [13, 5]⟩, ⟨1325, false, false, [289], [5]⟩,
    ⟨89, true, false, [289], [1283, 5]⟩, ⟨226, true, false, [], [1283, 5]⟩, ⟨1308, false, false,
    [291], []⟩]⟩
,
  ⟨[1335, 19], [1335, 19], .contexts []⟩
,
  ⟨[1335, 19], [293, 1281], .contexts [⟨1787, false, false, [], []⟩, ⟨1749, true, false, [],
    [19]⟩, ⟨1557, false, false, [1321], []⟩, ⟨1563, false, false, [1321], []⟩, ⟨1786, false,
    false, [], [15]⟩, ⟨1306, false, false, [291], []⟩, ⟨88, true, false, [291], [1281]⟩, ⟨227,
    true, false, [], [1281]⟩, ⟨1290, false, false, [293], []⟩, ⟨877, true, false, [], [293,
    1281]⟩]⟩
,
  ⟨[1335, 5], [185, 1315], .contexts [⟨1754, false, false, [], []⟩, ⟨1755, false, false, [],
    []⟩, ⟨1695, false, false, [], []⟩, ⟨1697, false, false, [], []⟩, ⟨1697, false, false, [],
    []⟩]⟩
,
  ⟨[1335, 17], [219, 1335], .contexts [⟨1772, false, false, [], []⟩, ⟨1774, false, false, [],
    []⟩, ⟨1768, false, false, [], []⟩, ⟨1769, false, false, [], []⟩, ⟨1769, false, false, [],
    []⟩]⟩
,
  ⟨[5, 17, 5, 17], [], .contexts [⟨53, false, false, [], []⟩]⟩
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
