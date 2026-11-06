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
def y422TPathRawData14 : Fin 128 → ℕ × ℕ :=
  ![(1791, 0),
    (1792, 5),
    (1793, 6),
    (1794, 0),
    (1795, 7),
    (1796, 8),
    (1797, 0),
    (1798, 1),
    (1799, 2),
    (1800, 0),
    (1801, 5),
    (1802, 6),
    (1803, 0),
    (1804, 7),
    (1805, 8),
    (1806, 0),
    (1807, 1),
    (1808, 2),
    (1809, 0),
    (1810, 5),
    (1811, 6),
    (1812, 0),
    (1813, 7),
    (1814, 8),
    (1815, 0),
    (1816, 1),
    (1817, 2),
    (1818, 0),
    (1819, 5),
    (1820, 6),
    (1821, 0),
    (1822, 7),
    (1823, 8),
    (1824, 0),
    (1825, 1),
    (1826, 2),
    (1827, 0),
    (165, 8),
    (1130, 1),
    (1350, 5),
    (1831, 6),
    (1832, 0),
    (1833, 7),
    (1834, 8),
    (1835, 0),
    (1836, 1),
    (1837, 2),
    (1838, 0),
    (1839, 5),
    (1840, 6),
    (1841, 0),
    (1842, 7),
    (1843, 8),
    (1844, 0),
    (1845, 1),
    (1846, 2),
    (1847, 0),
    (1848, 5),
    (1849, 6),
    (1850, 0),
    (1851, 7),
    (1852, 8),
    (1853, 0),
    (1854, 1),
    (1855, 2),
    (1856, 0),
    (1857, 5),
    (1858, 6),
    (1859, 0),
    (1860, 7),
    (1861, 8),
    (1862, 0),
    (1863, 1),
    (1864, 2),
    (1865, 0),
    (1866, 5),
    (1867, 6),
    (1868, 0),
    (1869, 7),
    (1870, 8),
    (1871, 0),
    (1872, 1),
    (1873, 2),
    (1874, 0),
    (1875, 5),
    (1876, 6),
    (1877, 0),
    (1878, 7),
    (1879, 8),
    (1880, 0),
    (1881, 1),
    (1882, 2),
    (1883, 0),
    (1884, 5),
    (1885, 6),
    (1886, 0),
    (1887, 7),
    (1888, 8),
    (1889, 0),
    (1890, 1),
    (1891, 2),
    (1892, 0),
    (43, 8),
    (160, 8),
    (1695, 7),
    (1491, 7),
    (1897, 8),
    (1622, 1),
    (1899, 2),
    (1900, 5),
    (1901, 6),
    (1902, 0),
    (1903, 7),
    (1286, 1),
    (1905, 2),
    (1906, 0),
    (1907, 5),
    (1908, 6),
    (1909, 0),
    (1910, 7),
    (1911, 8),
    (1912, 0),
    (1913, 1),
    (1914, 2),
    (1915, 0),
    (1916, 5),
    (1917, 6),
    (1918, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData14_allowed (j : Fin 128) :
    (1792 + j.val = 0 ∨ (y422TPathRawData14 j).1 < 1792 + j.val) ∧
      (y422TPathRawData14 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
