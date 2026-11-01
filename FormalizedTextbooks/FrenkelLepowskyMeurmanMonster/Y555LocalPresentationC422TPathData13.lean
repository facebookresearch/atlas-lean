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
def y422TPathRawData13 : Fin 128 → ℕ × ℕ :=
  ![(1663, 0),
    (1664, 5),
    (1665, 6),
    (1666, 0),
    (1667, 7),
    (1668, 8),
    (1669, 0),
    (1670, 1),
    (1671, 2),
    (1672, 0),
    (1673, 5),
    (1674, 6),
    (1675, 0),
    (1676, 7),
    (1677, 8),
    (1678, 0),
    (1679, 1),
    (1680, 2),
    (1681, 0),
    (1682, 5),
    (1683, 6),
    (1684, 0),
    (1685, 7),
    (1686, 8),
    (1687, 0),
    (1688, 1),
    (1689, 2),
    (1690, 0),
    (1691, 5),
    (1692, 6),
    (191, 8),
    (41, 8),
    (1695, 2),
    (1696, 7),
    (1697, 0),
    (1698, 1),
    (1211, 5),
    (1700, 6),
    (1701, 0),
    (1702, 7),
    (1703, 8),
    (1704, 0),
    (1705, 1),
    (1706, 2),
    (1707, 0),
    (1708, 5),
    (1709, 6),
    (1710, 0),
    (1711, 7),
    (1712, 8),
    (1713, 0),
    (1714, 1),
    (1715, 2),
    (1716, 0),
    (1717, 5),
    (1718, 6),
    (1719, 0),
    (1720, 7),
    (1721, 8),
    (1722, 0),
    (1723, 1),
    (1724, 2),
    (1725, 0),
    (1726, 5),
    (1727, 6),
    (1728, 0),
    (1729, 7),
    (1730, 8),
    (1731, 0),
    (1732, 1),
    (1733, 2),
    (1734, 0),
    (1735, 5),
    (1736, 6),
    (1737, 0),
    (1738, 7),
    (1739, 8),
    (1740, 0),
    (1741, 1),
    (1742, 2),
    (1743, 0),
    (1744, 5),
    (1745, 6),
    (1746, 0),
    (1747, 7),
    (1748, 8),
    (1749, 0),
    (1750, 1),
    (1751, 2),
    (1752, 0),
    (1753, 5),
    (1754, 6),
    (1755, 0),
    (1756, 7),
    (1757, 8),
    (1758, 0),
    (1759, 1),
    (1760, 2),
    (1761, 0),
    (1762, 5),
    (1763, 6),
    (217, 8),
    (1488, 1),
    (1280, 5),
    (1767, 6),
    (1768, 0),
    (1769, 7),
    (1770, 8),
    (1771, 1),
    (1772, 2),
    (1773, 0),
    (1774, 5),
    (1775, 6),
    (1776, 0),
    (1777, 7),
    (1778, 8),
    (1779, 0),
    (1780, 1),
    (1781, 2),
    (1782, 0),
    (1783, 5),
    (1784, 6),
    (1785, 0),
    (1786, 7),
    (1787, 8),
    (1788, 0),
    (1789, 1),
    (1790, 2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData13_allowed (j : Fin 128) :
    (1664 + j.val = 0 ∨ (y422TPathRawData13 j).1 < 1664 + j.val) ∧
      (y422TPathRawData13 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
