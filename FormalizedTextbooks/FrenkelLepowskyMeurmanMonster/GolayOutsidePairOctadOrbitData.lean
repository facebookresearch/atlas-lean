/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismGenerationData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOrthogonalOctadWords

/-! Original-codeword parent certificates for all330 octads outside the physical root pair. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Actual original encoder labels, in a checked root-first parent ordering. -/
def golayOutsidePairOctadNodeLabel : Fin 330 → Fin 4096 :=
  ![
  3, 224, 1713, 16, 1970, 2040, 10, 5, 75, 6, 9, 1665,
  1807, 1873, 215, 99, 208, 80, 54, 140, 176, 256, 1775, 448,
  1761, 1555, 1768, 1714, 1556, 1562, 1613, 1617, 1953, 123, 185, 63,
  48, 106, 32, 76, 1833, 1863, 1985, 2020, 190, 1940, 1906, 1880,
  459, 1967, 2036, 1890, 1960, 198, 41, 1813, 205, 13, 12, 155,
  1590, 38, 245, 1857, 14, 7, 1860, 202, 1802, 135, 152, 87,
  222, 1976, 1655, 57, 167, 1839, 134, 304, 291, 336, 1548, 1652,
  1735, 1666, 1729, 1716, 1618, 1601, 1798, 1855, 1876, 2045, 1969, 21,
  2017, 1764, 71, 235, 125, 157, 171, 1793, 112, 115, 149, 139,
  117, 249, 51, 1634, 58, 44, 64, 147, 160, 2001, 1762, 192,
  251, 82, 169, 96, 100, 26, 193, 172, 2018, 70, 2002, 238,
  1887, 25, 144, 128, 350, 272, 397, 313, 1682, 1606, 1791, 1631,
  1720, 1727, 394, 480, 320, 268, 384, 1778, 1567, 1587, 1589, 1577,
  150, 1752, 1583, 1608, 1780, 1633, 349, 1592, 1561, 1611, 1624, 1570,
  1580, 1710, 1662, 1675, 294, 1551, 446, 288, 1956, 229, 1905, 183,
  103, 221, 227, 85, 2035, 47, 217, 31, 1996, 237, 252, 109,
  92, 138, 1931, 1814, 1811, 1845, 1899, 1933, 1995, 1986, 37, 1921,
  1893, 118, 1866, 53, 2015, 1816, 2024, 126, 94, 1928, 1896, 2008,
  1908, 487, 327, 1983, 1919, 1938, 158, 60, 254, 1972, 28, 19,
  1834, 1849, 1827, 11, 65, 110, 1704, 1943, 189, 204, 212, 247,
  77, 461, 1640, 1542, 211, 162, 105, 1926, 1777, 74, 489, 1950,
  2004, 1804, 180, 242, 1636, 42, 174, 454, 1991, 1945, 1546, 1684,
  281, 1709, 1688, 331, 1681, 1755, 232, 35, 141, 91, 165, 218,
  1823, 230, 307, 277, 432, 1746, 1741, 1732, 1620, 1647, 1676, 1695,
  1650, 1912, 2046, 1869, 1954, 339, 1852, 1784, 203, 1842, 179, 89,
  186, 199, 1599, 240, 129, 1902, 22, 1537, 120, 1874, 2031, 494,
  284, 1657, 1738, 1758, 437, 332, 443, 1700, 266, 262, 1573, 314,
  1749, 391, 1671, 1699, 1828, 293]

/-- The earlier actual octad from which each noninitial node is reached. -/
def golayOutsidePairOctadNodeParent : Fin 330 → Fin 330 :=
  ![
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3,
  3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4,
  5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 7,
  7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8,
  8, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11,
  11, 11, 11, 11, 11, 11, 12, 12, 13, 13, 13, 13,
  13, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15,
  15, 15, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17,
  17, 17, 17, 17, 18, 18, 19, 19, 19, 19, 20, 20,
  20, 20, 20, 20, 21, 21, 21, 21, 22, 22, 22, 22,
  22, 22, 23, 23, 23, 23, 23, 24, 25, 25, 25, 25,
  26, 26, 26, 26, 26, 27, 27, 27, 27, 27, 27, 28,
  29, 30, 30, 30, 30, 31, 31, 31, 32, 32, 32, 33,
  33, 33, 34, 34, 35, 35, 35, 35, 36, 36, 37, 38,
  39, 39, 40, 40, 40, 40, 41, 41, 41, 42, 42, 42,
  43, 43, 43, 43, 43, 43, 43, 44, 44, 45, 46, 46,
  47, 48, 48, 49, 49, 50, 51, 51, 51, 52, 54, 54,
  55, 55, 55, 57, 58, 58, 59, 59, 59, 59, 59, 59,
  59, 60, 60, 60, 61, 62, 62, 63, 64, 65, 66, 66,
  66, 68, 70, 70, 71, 71, 72, 73, 73, 73, 74, 74,
  74, 74, 74, 74, 74, 74, 75, 75, 76, 76, 76, 76,
  77, 78, 80, 80, 81, 83, 85, 85, 85, 86, 86, 86,
  89, 92, 93, 94, 94, 96, 96, 97, 98, 103, 105, 106,
  106, 107, 118, 119, 119, 121, 122, 123, 124, 127, 132, 136,
  137, 141, 141, 142, 146, 146, 147, 148, 149, 149, 153, 153,
  155, 162, 165, 168, 183, 213]

/-- The genuine original strong-generator letter on each incoming edge. -/
def golayOutsidePairOctadNodeLetter : Fin 330 → Fin 28 :=
  ![
  4, 4, 5, 6, 7, 8, 10, 13, 22, 25, 27, 5,
  6, 7, 9, 11, 12, 13, 23, 25, 27, 6, 7, 8,
  9, 10, 11, 12, 22, 23, 25, 27, 7, 9, 10, 11,
  13, 23, 25, 8, 9, 10, 11, 13, 22, 23, 25, 27,
  5, 9, 12, 13, 25, 5, 6, 7, 22, 23, 27, 4,
  5, 6, 7, 8, 9, 10, 22, 5, 7, 9, 11, 12,
  25, 4, 5, 6, 7, 8, 22, 6, 7, 8, 9, 10,
  11, 12, 13, 22, 25, 27, 11, 12, 8, 9, 13, 22,
  27, 5, 11, 12, 13, 25, 27, 4, 7, 12, 13, 22,
  23, 27, 4, 5, 9, 10, 22, 25, 27, 4, 5, 8,
  9, 10, 11, 22, 5, 27, 4, 12, 22, 27, 4, 6,
  7, 10, 12, 22, 7, 12, 23, 25, 8, 11, 12, 13,
  22, 25, 9, 12, 13, 23, 27, 12, 11, 12, 13, 27,
  5, 6, 8, 10, 12, 4, 7, 8, 10, 25, 27, 27,
  27, 4, 12, 13, 22, 6, 7, 8, 8, 22, 27, 11,
  12, 27, 13, 27, 4, 13, 23, 27, 7, 9, 27, 7,
  12, 13, 10, 12, 13, 27, 12, 13, 27, 12, 22, 27,
  5, 6, 7, 8, 9, 10, 12, 25, 27, 12, 9, 27,
  12, 12, 13, 12, 27, 27, 6, 8, 22, 12, 11, 13,
  12, 13, 27, 13, 5, 8, 5, 7, 9, 10, 11, 13,
  25, 8, 10, 11, 10, 9, 13, 9, 5, 22, 5, 11,
  25, 27, 12, 13, 5, 22, 27, 5, 11, 23, 6, 7,
  8, 9, 11, 22, 23, 27, 9, 11, 8, 9, 10, 22,
  12, 11, 12, 13, 13, 27, 11, 13, 25, 4, 7, 10,
  12, 12, 12, 10, 12, 5, 23, 12, 27, 12, 11, 5,
  12, 13, 22, 12, 23, 22, 22, 5, 12, 22, 27, 27,
  11, 12, 27, 23, 12, 27, 23, 8, 13, 27, 13, 22,
  10, 11, 13, 22, 22, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
-- Check the original encoder bits for every displayed physical octad.
/-- Every node is an actual original octad with both physical root coordinates absent. -/
theorem golayOutsidePairOctad_node_member : ∀ n : Fin 330,
    golayOutsidePairOctadNodeLabel n ∈ generatedFeasibleOctadsOutsideRootPair := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
-- Check every pair of original encoder labels, without assuming catalogue recognition.
/-- Distinct parent addresses represent distinct original octads. -/
theorem golayOutsidePairOctad_node_injective :
    Function.Injective golayOutsidePairOctadNodeLabel := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
-- All noninitial parent addresses are strictly earlier.
/-- Every noninitial node has a strictly earlier actual parent. -/
theorem golayOutsidePairOctad_parent_lt : ∀ n : Fin 330, n ≠ 0 →
    (golayOutsidePairOctadNodeParent n).val < n.val := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
-- Check physical root fixation by every actual incoming strong-generator array.
/-- Every incoming letter fixes the two original physical root coordinates pointwise. -/
theorem golayOutsidePairOctad_letter_fix_pair : ∀ n : Fin 330,
    golayStrongLetterArray (golayOutsidePairOctadNodeLetter n) 0 = 0 ∧
      golayStrongLetterArray (golayOutsidePairOctadNodeLetter n) 1 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
-- Each of the330 parent edges is checked on all24 original source-codeword bits.
/-- Each noninitial parent octad is carried to its child by the stated original letter. -/
theorem golayOutsidePairOctad_edge_bits : ∀ n : Fin 330, n ≠ 0 → ∀ i : Fin 24,
    (golayEncodedMask
      (golayOutsidePairOctadNodeLabel (golayOutsidePairOctadNodeParent n)).val).testBit i.val =
      (golayEncodedMask (golayOutsidePairOctadNodeLabel n).val).testBit
        (golayStrongLetterArray (golayOutsidePairOctadNodeLetter n) i).val := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
