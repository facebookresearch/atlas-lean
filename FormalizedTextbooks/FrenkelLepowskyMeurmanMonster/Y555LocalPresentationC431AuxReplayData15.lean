/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal chronological equation data for the original-source C431 replay, block 15. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawContextPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Exact raw source or earlier-equation contextual derivations, chronological block 15. -/
def y431AuxReplayData15 : Fin 128 → Y322RawContextCertificate :=
![
  ⟨[3, 17, 3, 17], [], .contexts [⟨179, false, false, [], []⟩]⟩
,
  ⟨[3, 17], [16, 2], .contexts [⟨1920, false, false, [], [16, 2]⟩]⟩
,
  ⟨[16, 2], [17, 3], .contexts [⟨938, false, false, [], [2]⟩, ⟨888, false, false, [17], []⟩]⟩
,
  ⟨[1337, 19], [1337, 19], .contexts []⟩
,
  ⟨[1337, 19], [331, 1287], .contexts [⟨1923, false, false, [], []⟩, ⟨1898, true, false, [],
    [19]⟩, ⟨1744, false, false, [1315], []⟩, ⟨1745, false, false, [1315], []⟩, ⟨1814, false,
    false, [], [3]⟩, ⟨1821, false, false, [299], []⟩, ⟨247, true, false, [], [1287]⟩, ⟨1360,
    false, false, [331], []⟩, ⟨877, true, false, [], [331, 1287]⟩]⟩
,
  ⟨[331, 1287], [331, 1287], .contexts []⟩
,
  ⟨[1287, 1], [1287, 1], .contexts []⟩
,
  ⟨[1287, 1], [337, 1287], .contexts [⟨1926, false, false, [], []⟩, ⟨248, false, false, [332],
    [1287, 1]⟩, ⟨1924, true, false, [332, 211], [1]⟩, ⟨1902, true, false, [332], [19, 1]⟩,
    ⟨1902, true, false, [332], [19, 1]⟩, ⟨1901, true, false, [332], [19, 1]⟩, ⟨1907, true,
    false, [332], [19, 1]⟩, ⟨1905, true, false, [332], [19, 1]⟩, ⟨1570, false, false, [332,
    1337], [18]⟩, ⟨984, false, false, [332, 1337], []⟩, ⟨1923, false, false, [332], []⟩, ⟨1924,
    false, false, [332], []⟩, ⟨1925, false, false, [332], []⟩, ⟨1925, false, false, [332], []⟩,
    ⟨1360, false, false, [332, 331], []⟩, ⟨249, true, false, [], [331, 1287]⟩, ⟨250, true,
    false, [], [1287]⟩]⟩
,
  ⟨[1337, 11], [309, 1309], .contexts [⟨1912, false, false, [], []⟩, ⟨1913, false, false, [],
    []⟩, ⟨1824, false, false, [], []⟩, ⟨1825, false, false, [], []⟩, ⟨1825, false, false, [],
    []⟩]⟩
,
  ⟨[1309, 5], [1309, 5], .contexts []⟩
,
  ⟨[1309, 5], [338, 309, 1309], .contexts [⟨251, false, false, [338], [1309, 5]⟩, ⟨1913, true,
    false, [338, 329], [5]⟩, ⟨1909, true, false, [338], [11, 5]⟩, ⟨1909, true, false, [338],
    [11, 5]⟩, ⟨1908, true, false, [338], [11, 5]⟩, ⟨877, false, false, [338], [329, 1337, 11,
    5]⟩, ⟨1911, true, false, [338], [11, 5]⟩, ⟨1910, true, false, [338], [11, 5]⟩, ⟨1857, false,
    false, [338, 1337], []⟩, ⟨926, false, false, [338, 1337], []⟩, ⟨1928, false, false, [338],
    []⟩]⟩
,
  ⟨[1337, 13, 11], [197, 309, 1309], .contexts [⟨1918, false, false, [], [11]⟩, ⟨1918, false,
    false, [], [11]⟩, ⟨1898, true, false, [], [13, 11]⟩, ⟨1271, false, false, [1315], [11]⟩,
    ⟨1272, false, false, [1315], [11]⟩, ⟨1690, false, false, [], [3, 11]⟩, ⟨1692, false, false,
    [], [3, 11]⟩, ⟨1915, false, false, [], [3, 11]⟩, ⟨1915, false, false, [], [3, 11]⟩, ⟨1895,
    false, false, [197], [11]⟩, ⟨1916, false, false, [], [11]⟩, ⟨1917, false, false, [], [11]⟩,
    ⟨1906, false, false, [197], [11]⟩, ⟨877, true, false, [], [197, 1337, 11]⟩, ⟨1916, false,
    false, [], [11]⟩, ⟨1917, false, false, [], [11]⟩, ⟨1917, false, false, [], [11]⟩, ⟨1913,
    false, false, [197], []⟩]⟩
,
  ⟨[337, 1287], [337, 1287], .contexts []⟩
,
  ⟨[1287, 1], [337, 1287], .contexts [⟨1926, false, false, [], []⟩, ⟨1927, false, false, [],
    []⟩, ⟨1932, false, false, [], []⟩, ⟨1932, false, false, [], []⟩]⟩
,
  ⟨[1291, 11], [1291, 11], .contexts []⟩
,
  ⟨[336], [336], .contexts []⟩
,
  ⟨[343, 1309], [343, 1309], .contexts []⟩
,
  ⟨[1309, 5], [343, 1309], .contexts [⟨1929, false, false, [], []⟩, ⟨1929, false, false, [],
    []⟩, ⟨1930, false, false, [], []⟩, ⟨1485, false, false, [338, 309], []⟩, ⟨252, true, false,
    [], [309, 1309]⟩, ⟨253, true, false, [], [1309]⟩, ⟨1936, false, false, [], []⟩, ⟨1936,
    false, false, [], []⟩]⟩
,
  ⟨[343, 1305], [343, 1305], .contexts []⟩
,
  ⟨[343, 1305], [343, 1305], .contexts []⟩
,
  ⟨[5, 13, 5, 13], [], .contexts [⟨1320, false, false, [], []⟩]⟩
,
  ⟨[1305, 13], [1305, 13], .contexts []⟩
,
  ⟨[342], [342], .contexts []⟩
,
  ⟨[351], [342], .contexts [⟨257, false, false, [], []⟩, ⟨1942, false, false, [], []⟩, ⟨1942,
    false, false, [], []⟩]⟩
,
  ⟨[1305, 13], [351, 1309], .contexts [⟨1941, false, false, [], []⟩, ⟨1939, true, false, [342],
    [13]⟩, ⟨1938, true, false, [342], [13]⟩, ⟨1468, true, false, [], [13]⟩, ⟨1478, true, false,
    [], [5, 13]⟩, ⟨1937, true, false, [342], [13, 5, 13]⟩, ⟨1940, false, false, [342, 1309],
    []⟩, ⟨1485, false, false, [342], []⟩, ⟨1943, true, false, [], [1309]⟩]⟩
,
  ⟨[343], [350], .contexts [⟨257, true, true, [], []⟩]⟩
,
  ⟨[343], [343], .contexts []⟩
,
  ⟨[343], [343], .contexts []⟩
,
  ⟨[343], [343], .contexts []⟩
,
  ⟨[1307], [343, 1305], .contexts [⟨1846, true, false, [], []⟩, ⟨1944, true, false, [350],
    [13]⟩, ⟨18, false, false, [350, 1305], []⟩, ⟨1945, true, false, [], [1305]⟩, ⟨1938, false,
    false, [], []⟩, ⟨1948, true, false, [], [1305]⟩, ⟨1947, true, false, [], [1305]⟩, ⟨1946,
    true, false, [], [1305]⟩]⟩
,
  ⟨[1307], [343, 1305], .contexts [⟨1949, false, false, [], []⟩, ⟨1939, false, false, [], []⟩]⟩
,
  ⟨[351, 1309], [351, 1309], .contexts []⟩
,
  ⟨[359, 1303, 13], [1303], .contexts [⟨1459, true, false, [359], [13]⟩, ⟨261, false, false, [],
    [1305, 15, 13]⟩, ⟨1950, true, false, [357], [15, 13]⟩, ⟨1478, true, false, [357], [15, 13]⟩,
    ⟨260, false, false, [], [1309, 13, 15, 13]⟩, ⟨1722, true, false, [351], [13, 15, 13]⟩,
    ⟨1951, true, false, [], [15, 13, 15, 13]⟩, ⟨1951, true, false, [], [15, 13, 15, 13]⟩, ⟨1944,
    true, false, [], [15, 13, 15, 13]⟩, ⟨1941, true, false, [], [15, 13, 15, 13]⟩, ⟨968, false,
    false, [1305], [14]⟩, ⟨1881, false, false, [], []⟩, ⟨1880, false, false, [], []⟩]⟩
,
  ⟨[1303, 13], [1303, 13], .contexts []⟩
,
  ⟨[358], [358], .contexts []⟩
,
  ⟨[1307], [343, 1305], .contexts [⟨1950, false, false, [], []⟩]⟩
,
  ⟨[343, 1305, 15], [343, 1303], .contexts [⟨1459, false, false, [343], []⟩]⟩
,
  ⟨[343, 1303], [343, 1303], .contexts []⟩
,
  ⟨[343, 1303], [343, 1303], .contexts []⟩
,
  ⟨[343, 1303], [343, 1303], .contexts []⟩
,
  ⟨[1303, 5], [1303, 5], .contexts []⟩
,
  ⟨[343], [343], .contexts [⟨877, false, false, [], [343]⟩, ⟨1947, false, false, [], []⟩, ⟨1948,
    false, false, [], []⟩]⟩
,
  ⟨[1303, 1], [1301], .contexts [⟨1543, false, false, [], []⟩, ⟨1443, false, false, [], []⟩,
    ⟨1444, false, false, [], []⟩, ⟨1444, false, false, [], []⟩]⟩
,
  ⟨[361, 1303], [361, 1303], .contexts []⟩
,
  ⟨[1303, 0], [1303, 1], .contexts [⟨871, false, false, [1303], []⟩]⟩
,
  ⟨[361, 1301, 13], [1303, 1], .contexts [⟨1451, true, false, [361], [13]⟩, ⟨1963, true, false,
    [], [1, 13]⟩, ⟨1963, true, false, [], [1, 13]⟩, ⟨262, false, false, [], [1303, 1, 13]⟩,
    ⟨1954, false, false, [], [1303, 1, 13]⟩, ⟨1954, false, false, [], [1303, 1, 13]⟩, ⟨1457,
    true, false, [358], [1, 13]⟩, ⟨1952, true, false, [358], [1, 13]⟩, ⟨1953, true, false, [],
    [1, 13]⟩, ⟨1953, true, false, [], [1, 13]⟩, ⟨1689, false, false, [1303], []⟩, ⟨1964, false,
    false, [], []⟩]⟩
,
  ⟨[360], [360], .contexts []⟩
,
  ⟨[1301, 13], [359, 1301], .contexts [⟨1965, false, false, [360], []⟩, ⟨1962, false, false,
    [360], []⟩, ⟨1449, false, false, [360], []⟩, ⟨1966, true, false, [], [1301]⟩, ⟨1966, true,
    false, [], [1301]⟩, ⟨262, false, true, [], [1301]⟩]⟩
,
  ⟨[343, 1303, 1], [343, 1301], .contexts [⟨1451, false, false, [343], []⟩]⟩
,
  ⟨[343, 1301], [343, 1301], .contexts []⟩
,
  ⟨[343, 1301], [343, 1301], .contexts []⟩
,
  ⟨[343, 1301], [343, 1301], .contexts []⟩
,
  ⟨[1303, 5, 1, 5], [343, 1301, 5], .contexts [⟨1960, false, false, [], [1, 5]⟩, ⟨1960, false,
    false, [], [1, 5]⟩, ⟨1880, true, false, [], [5, 1, 5]⟩, ⟨899, false, false, [1305], [1, 5]⟩,
    ⟨901, false, false, [1305], [1, 5]⟩, ⟨1469, false, false, [], [15, 1, 5]⟩, ⟨1955, false,
    false, [], [15, 1, 5]⟩, ⟨1939, false, false, [], [15, 1, 5]⟩, ⟨1939, false, false, [], [15,
    1, 5]⟩, ⟨1956, false, false, [], [1, 5]⟩, ⟨1957, false, false, [], [1, 5]⟩, ⟨1958, false,
    false, [], [1, 5]⟩, ⟨1959, false, false, [], [1, 5]⟩, ⟨1457, false, false, [343], [1, 5]⟩,
    ⟨1961, true, false, [], [1303, 1, 5]⟩, ⟨1957, false, false, [], [1, 5]⟩, ⟨1959, false,
    false, [], [1, 5]⟩, ⟨1959, false, false, [], [1, 5]⟩, ⟨1968, false, false, [], [5]⟩, ⟨1969,
    false, false, [], [5]⟩, ⟨1970, false, false, [], [5]⟩, ⟨1971, false, false, [], [5]⟩]⟩
,
  ⟨[1301, 5], [1301, 5], .contexts []⟩
,
  ⟨[1301, 5], [351, 1301], .contexts [⟨1973, false, false, [], []⟩, ⟨1972, true, false, [342],
    []⟩, ⟨1868, false, false, [342, 1303], [0]⟩, ⟨1964, false, false, [342], []⟩, ⟨1962, false,
    false, [342], []⟩, ⟨1449, false, false, [342], []⟩, ⟨1943, true, false, [], [1301]⟩]⟩
,
  ⟨[351, 1301], [351, 1301], .contexts []⟩
,
  ⟨[1301, 11], [1299], .contexts [⟨1544, false, false, [], []⟩]⟩
,
  ⟨[1299, 5], [1299, 5], .contexts []⟩
,
  ⟨[350], [350], .contexts []⟩
,
  ⟨[1299, 5], [343, 1299], .contexts [⟨1977, false, false, [], []⟩, ⟨1442, true, false, [],
    [5]⟩, ⟨1975, true, false, [350], [11, 5]⟩, ⟨1975, true, false, [350], [11, 5]⟩, ⟨1974, true,
    false, [350], [11, 5]⟩, ⟨1973, true, false, [350], [11, 5]⟩, ⟨1857, false, false, [350,
    1301], []⟩, ⟨926, false, false, [350, 1301], []⟩, ⟨1976, false, false, [350], []⟩, ⟨1434,
    false, false, [350], []⟩, ⟨1435, false, false, [350], []⟩, ⟨1435, false, false, [350], []⟩,
    ⟨1440, false, false, [350], []⟩, ⟨1978, true, false, [], [1299]⟩, ⟨1978, true, false, [],
    [1299]⟩, ⟨1945, true, false, [], [1299]⟩, ⟨1946, true, false, [], [1299]⟩]⟩
,
  ⟨[343, 1299], [343, 1299], .contexts []⟩
,
  ⟨[1299, 5, 3, 5, 3, 5], [363, 343, 1299], .contexts [⟨1977, false, false, [], [3, 5, 3, 5]⟩,
    ⟨1979, false, false, [], [3, 5, 3, 5]⟩, ⟨1980, false, false, [], [3, 5, 3, 5]⟩, ⟨1980,
    false, false, [], [3, 5, 3, 5]⟩, ⟨1432, false, false, [343], [5, 3, 5]⟩, ⟨1894, true, false,
    [343, 324], [5, 3, 5]⟩, ⟨1893, true, false, [343, 324], [5, 3, 5]⟩, ⟨1892, true, false,
    [343, 324], [5, 3, 5]⟩, ⟨1891, true, false, [343, 324], [5, 3, 5]⟩, ⟨1791, false, false,
    [343, 324, 1295], [16, 3, 5]⟩, ⟨938, false, false, [343, 324, 1295], [3, 5]⟩, ⟨1425, false,
    false, [343, 324], [3, 5]⟩, ⟨1430, false, false, [343, 324], [3, 5]⟩, ⟨1871, true, false,
    [343], [1297, 3, 5]⟩, ⟨263, true, false, [], [1297, 3, 5]⟩, ⟨1431, false, false, [363],
    [5]⟩, ⟨1979, false, false, [363], []⟩]⟩
,
  ⟨[365, 1297], [365, 1297], .contexts []⟩
,
  ⟨[365], [365], .contexts []⟩
,
  ⟨[1299], [365, 1297], .contexts [⟨1440, false, false, [], []⟩, ⟨1840, true, false, [1299],
    []⟩, ⟨1981, false, false, [], [3]⟩, ⟨264, true, false, [], [1299, 3]⟩, ⟨1432, false, false,
    [365], []⟩, ⟨1982, false, false, [], []⟩, ⟨1983, true, false, [], [1297]⟩]⟩
,
  ⟨[1299], [365, 1297], .contexts [⟨1984, false, false, [], []⟩, ⟨1982, false, false, [], []⟩]⟩
,
  ⟨[364], [364], .contexts []⟩
,
  ⟨[1297, 11], [367, 1301], .contexts [⟨1984, true, false, [364], [11]⟩, ⟨1441, false, false,
    [364], []⟩, ⟨1443, false, false, [364], []⟩, ⟨1986, true, false, [], [1301]⟩, ⟨1986, true,
    false, [], [1301]⟩, ⟨265, true, false, [], [1301]⟩]⟩
,
  ⟨[1297, 17], [1295], .contexts [⟨1546, false, false, [], []⟩, ⟨1414, false, false, [], []⟩,
    ⟨1415, false, false, [], []⟩, ⟨1415, false, false, [], []⟩]⟩
,
  ⟨[1299], [365, 1297], .contexts [⟨1985, false, false, [], []⟩]⟩
,
  ⟨[1297, 3], [365, 1297], .contexts [⟨1433, false, false, [], []⟩, ⟨1989, false, false, [],
    []⟩, ⟨1982, false, false, [], []⟩, ⟨1982, false, false, [], []⟩]⟩
,
  ⟨[365, 1297, 17], [365, 1295], .contexts [⟨1422, false, false, [365], []⟩]⟩
,
  ⟨[365, 1295], [365, 1295], .contexts []⟩
,
  ⟨[365, 1295], [365, 1295], .contexts []⟩
,
  ⟨[365, 1295], [365, 1295], .contexts []⟩
,
  ⟨[1295, 3], [1295, 3], .contexts []⟩
,
  ⟨[365, 1295], [365, 1295], .contexts [⟨1420, false, false, [365], []⟩]⟩
,
  ⟨[365, 1295], [365, 1295], .contexts [⟨1983, true, false, [], [1295]⟩, ⟨877, true, false, [],
    [365, 1295]⟩]⟩
,
  ⟨[367, 1301], [367, 1301], .contexts []⟩
,
  ⟨[367, 1301], [367, 1301], .contexts []⟩
,
  ⟨[1301, 3], [1301, 3], .contexts []⟩
,
  ⟨[367], [367], .contexts [⟨877, false, false, [], [367]⟩]⟩
,
  ⟨[369, 1291, 3], [1295, 13], .contexts [⟨266, false, false, [], [1291, 3]⟩, ⟨1877, true,
    false, [365], [3]⟩, ⟨1413, true, false, [365], [3]⟩, ⟨1994, true, false, [], [13, 3]⟩,
    ⟨1994, true, false, [], [13, 3]⟩, ⟨1992, true, false, [], [13, 3]⟩, ⟨1997, true, false, [],
    [13, 3]⟩, ⟨1996, true, false, [], [13, 3]⟩, ⟨1994, true, false, [], [13, 3]⟩, ⟨1993, true,
    false, [], [13, 3]⟩, ⟨1992, true, false, [], [13, 3]⟩, ⟨1991, true, false, [], [13, 3]⟩,
    ⟨1990, true, false, [], [17, 13, 3]⟩, ⟨1732, true, false, [1297], [13, 3]⟩, ⟨1731, true,
    false, [1297], [13, 3]⟩, ⟨1988, false, false, [], [3, 13, 3]⟩, ⟨1995, true, false, [], [13,
    3]⟩, ⟨1995, true, false, [], [13, 3]⟩, ⟨1270, false, false, [1295], [12]⟩, ⟨951, false,
    false, [1295], []⟩]⟩
,
  ⟨[1309, 1], [1339], .contexts [⟨269, true, false, [], []⟩]⟩
,
  ⟨[1339, 1], [1309], .contexts [⟨2003, true, false, [], [1]⟩, ⟨4, false, false, [1309], []⟩,
    ⟨1480, false, false, [], []⟩]⟩
,
  ⟨[1339], [1339], .contexts []⟩
,
  ⟨[1339], [1339], .contexts []⟩
,
  ⟨[1309, 1], [1339], .contexts [⟨2003, false, false, [], []⟩, ⟨2005, false, false, [], []⟩,
    ⟨2006, false, false, [], []⟩, ⟨2006, false, false, [], []⟩]⟩
,
  ⟨[1309, 3, 1], [375, 1313], .contexts [⟨1826, false, false, [], [1]⟩, ⟨1831, false, false, [],
    [1]⟩, ⟨1805, false, false, [], [1]⟩, ⟨1806, false, false, [], [1]⟩, ⟨1806, false, false, [],
    [1]⟩, ⟨1494, true, false, [297], [1]⟩, ⟨1499, true, false, [297], [11, 1]⟩, ⟨1682, true,
    false, [297, 188], [11, 1]⟩, ⟨1684, false, false, [297, 188, 1317], [0, 10]⟩, ⟨1685, false,
    false, [297, 188, 1317], []⟩, ⟨1683, false, false, [297, 188], [11]⟩, ⟨1536, false, false,
    [297, 188], []⟩, ⟨1491, false, false, [297, 188], []⟩, ⟨1492, false, false, [297, 188], []⟩,
    ⟨1492, false, false, [297, 188], []⟩, ⟨1493, false, false, [297, 188], []⟩, ⟨1686, true,
    false, [297], [1313]⟩, ⟨1686, true, false, [297], [1313]⟩, ⟨174, true, false, [297],
    [1313]⟩, ⟨270, true, false, [], [1313]⟩]⟩
,
  ⟨[377, 1339], [377, 1339], .contexts []⟩
,
  ⟨[377, 1339], [377, 1339], .contexts []⟩
,
  ⟨[377, 1339], [377, 1339], .contexts []⟩
,
  ⟨[1339, 3], [1339, 3], .contexts []⟩
,
  ⟨[1339], [1339], .contexts []⟩
,
  ⟨[377], [377], .contexts [⟨877, false, false, [], [377]⟩]⟩
,
  ⟨[343, 1339], [343, 1339], .contexts []⟩
,
  ⟨[343, 1339], [343, 1339], .contexts []⟩
,
  ⟨[1339, 5], [1339, 5], .contexts []⟩
,
  ⟨[1339, 5], [343, 1339], .contexts [⟨2017, false, false, [], []⟩, ⟨2007, true, false, [],
    [5]⟩, ⟨1153, false, false, [1309], []⟩, ⟨1154, false, false, [1309], []⟩, ⟨1937, false,
    false, [], [1]⟩, ⟨2003, false, false, [343], []⟩, ⟨2015, false, false, [], []⟩, ⟨2016,
    false, false, [], []⟩, ⟨2013, false, false, [343], []⟩, ⟨1961, true, false, [], [1339]⟩]⟩
,
  ⟨[9, 1339], [9, 1339], .contexts []⟩
,
  ⟨[9, 1339], [9, 1339], .contexts []⟩
,
  ⟨[1339, 9], [1339, 9], .contexts []⟩
,
  ⟨[1309, 11], [297, 1337], .contexts [⟨1914, false, false, [], []⟩, ⟨1919, false, false, [],
    []⟩, ⟨1919, false, false, [], []⟩]⟩
,
  ⟨[381, 1339], [381, 1339], .contexts []⟩
,
  ⟨[381, 1339], [381, 1339], .contexts []⟩
,
  ⟨[1339, 11], [1339, 11], .contexts []⟩
,
  ⟨[381], [381], .contexts [⟨877, false, false, [], [381]⟩]⟩
,
  ⟨[181, 1309], [181, 1309], .contexts []⟩
,
  ⟨[181, 1339], [181, 1339], .contexts []⟩
,
  ⟨[181, 1339], [181, 1339], .contexts []⟩
,
  ⟨[1339, 15], [1339, 15], .contexts []⟩
,
  ⟨[1339, 15], [181, 1339], .contexts [⟨2030, false, false, [], []⟩, ⟨2007, true, false, [],
    [15]⟩, ⟨1188, false, false, [1309], []⟩, ⟨1189, false, false, [1309], []⟩, ⟨1721, false,
    false, [], [1]⟩, ⟨1722, false, false, [], [1]⟩, ⟨2027, false, false, [], [1]⟩, ⟨2027, false,
    false, [], [1]⟩, ⟨2003, false, false, [181], []⟩, ⟨2028, false, false, [], []⟩, ⟨2029,
    false, false, [], []⟩, ⟨2013, false, false, [181], []⟩, ⟨1672, true, false, [], [1339]⟩]⟩
,
  ⟨[1309, 11, 3, 17, 13, 5, 15], [389, 1335], .contexts [⟨2022, false, false, [], [3, 17, 13, 5,
    15]⟩, ⟨1896, false, false, [297], [17, 13, 5, 15]⟩, ⟨1802, false, false, [], [17, 13, 5,
    15]⟩, ⟨1803, false, false, [], [17, 13, 5, 15]⟩, ⟨1795, false, false, [297], [13, 5, 15]⟩,
    ⟨274, true, false, [], [1315, 13, 5, 15]⟩, ⟨1692, false, false, [383], [5, 15]⟩, ⟨275, true,
    false, [], [1315, 5, 15]⟩, ⟨1756, false, false, [385], [15]⟩, ⟨276, true, false, [], [1335,
    15]⟩, ⟨1766, false, false, [387], []⟩, ⟨277, true, false, [], [1335]⟩]⟩
,
  ⟨[1309, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13], [395, 1327], .contexts [⟨2032, false, false,
    [], [1, 11, 3, 17, 13]⟩, ⟨1747, false, false, [389], [11, 3, 17, 13]⟩, ⟨1656, false, false,
    [389], [3, 17, 13]⟩, ⟨278, true, false, [], [1321, 3, 17, 13]⟩, ⟨1735, false, false, [391],
    [17, 13]⟩, ⟨279, true, false, [], [1333, 17, 13]⟩, ⟨1724, false, false, [393], [13]⟩, ⟨1610,
    false, false, [393], []⟩, ⟨280, true, false, [], [1327]⟩]⟩
,
  ⟨[1309, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3], [405, 1265], .contexts
    [⟨2033, false, false, [], [5, 15, 1, 11, 3]⟩, ⟨1606, false, false, [395], [15, 1, 11, 3]⟩,
    ⟨281, true, false, [], [1327, 15, 1, 11, 3]⟩, ⟨1612, false, false, [397], [1, 11, 3]⟩, ⟨282,
    true, false, [], [1327, 1, 11, 3]⟩, ⟨1605, false, false, [399], [11, 3]⟩, ⟨283, true, false,
    [], [1331, 11, 3]⟩, ⟨1585, false, false, [401], [3]⟩, ⟨284, true, false, [], [1265, 3]⟩,
    ⟨957, false, false, [403], []⟩, ⟨98, true, false, [403], [1265]⟩, ⟨285, true, false, [],
    [1265]⟩]⟩
,
  ⟨[1309, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1], [411],
    .contexts [⟨2034, false, false, [], [17, 13, 5, 15, 1]⟩, ⟨977, false, false, [405], [13, 5,
    15, 1]⟩, ⟨100, true, false, [405], [1265, 13, 5, 15, 1]⟩, ⟨286, true, false, [], [1265, 13,
    5, 15, 1]⟩, ⟨944, false, false, [407], [5, 15, 1]⟩, ⟨904, false, false, [407], [15, 1]⟩,
    ⟨95, true, false, [407], [1263, 15, 1]⟩, ⟨287, true, false, [], [1263, 15, 1]⟩, ⟨858, false,
    false, [409], [1]⟩, ⟨92, true, false, [409], []⟩, ⟨288, true, false, [], []⟩]⟩
,
  ⟨[1309, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5], [421], .contexts [⟨2035, false, false, [], [11, 3, 17, 13, 5]⟩, ⟨89, true, false,
    [411], [3, 17, 13, 5]⟩, ⟨289, true, false, [], [3, 17, 13, 5]⟩, ⟨98, true, false, [413],
    [17, 13, 5]⟩, ⟨290, true, false, [], [17, 13, 5]⟩, ⟨100, true, false, [415], [13, 5]⟩, ⟨291,
    true, false, [], [13, 5]⟩, ⟨88, true, false, [417], [5]⟩, ⟨292, true, false, [], [5]⟩, ⟨95,
    true, false, [419], []⟩, ⟨293, true, false, [], []⟩]⟩
,
  ⟨[1309, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5, 15, 1, 11, 3, 17], [429, 1263], .contexts [⟨2036, false, false, [], [15, 1, 11, 3,
    17]⟩, ⟨856, false, false, [421], [1, 11, 3, 17]⟩, ⟨879, false, false, [421], [11, 3, 17]⟩,
    ⟨92, true, false, [421], [1263, 11, 3, 17]⟩, ⟨294, true, false, [], [1263, 11, 3, 17]⟩,
    ⟨929, false, false, [423], [3, 17]⟩, ⟨89, true, false, [423], [1263, 3, 17]⟩, ⟨295, true,
    false, [], [1263, 3, 17]⟩, ⟨892, false, false, [425], [17]⟩, ⟨98, true, false, [425], [1263,
    17]⟩, ⟨296, true, false, [], [1263, 17]⟩, ⟨942, false, false, [427], []⟩, ⟨100, true, false,
    [427], [1263]⟩, ⟨297, true, false, [], [1263]⟩]⟩
,
  ⟨[1309, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11], [437, 1331], .contexts [⟨2037, false, false, [],
    [13, 5, 15, 1, 11]⟩, ⟨943, false, false, [429], [5, 15, 1, 11]⟩, ⟨960, false, false, [429],
    [15, 1, 11]⟩, ⟨95, true, false, [429], [1265, 15, 1, 11]⟩, ⟨298, true, false, [], [1265, 15,
    1, 11]⟩, ⟨973, false, false, [431], [1, 11]⟩, ⟨88, true, false, [431], [1265, 1, 11]⟩, ⟨299,
    true, false, [], [1265, 1, 11]⟩, ⟨954, false, false, [433], [11]⟩, ⟨92, true, false, [433],
    [1265, 11]⟩, ⟨300, true, false, [], [1265, 11]⟩, ⟨1584, false, false, [435], []⟩, ⟨301,
    true, false, [], [1331]⟩]⟩
,
  ⟨[1309, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15], [447, 1331], .contexts [⟨2038,
    false, false, [], [3, 17, 13, 5, 15]⟩, ⟨1580, false, false, [437], [17, 13, 5, 15]⟩, ⟨302,
    true, false, [], [1331, 17, 13, 5, 15]⟩, ⟨1595, false, false, [439], [13, 5, 15]⟩, ⟨303,
    true, false, [], [1331, 13, 5, 15]⟩, ⟨1588, false, false, [441], [5, 15]⟩, ⟨304, true,
    false, [], [1331, 5, 15]⟩, ⟨1582, false, false, [443], [15]⟩, ⟨305, true, false, [], [1331,
    15]⟩, ⟨1592, false, false, [445], []⟩, ⟨306, true, false, [], [1331]⟩]⟩
,
  ⟨[1309, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13], [455, 1321],
    .contexts [⟨2039, false, false, [], [1, 11, 3, 17, 13]⟩, ⟨1526, false, false, [447], [11, 3,
    17, 13]⟩, ⟨1602, false, false, [447], [11, 3, 17, 13]⟩, ⟨307, true, false, [], [1327, 11, 3,
    17, 13]⟩, ⟨1522, false, false, [449], [3, 17, 13]⟩, ⟨1602, false, false, [449], [3, 17,
    13]⟩, ⟨308, true, false, [], [1327, 3, 17, 13]⟩, ⟨1519, false, false, [451], [17, 13]⟩,
    ⟨1515, false, false, [451], [13]⟩, ⟨1655, false, false, [451], [13]⟩, ⟨309, true, false, [],
    [1321, 13]⟩, ⟨1510, false, false, [453], []⟩, ⟨1655, false, false, [453], []⟩, ⟨310, true,
    false, [], [1321]⟩]⟩
,
  ⟨[1309, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11,
    3], [461, 1309], .contexts [⟨2040, false, false, [], [5, 15, 1, 11, 3]⟩, ⟨1506, false,
    false, [455], [15, 1, 11, 3]⟩, ⟨1678, false, false, [455], [15, 1, 11, 3]⟩, ⟨311, true,
    false, [], [1317, 15, 1, 11, 3]⟩, ⟨1502, false, false, [457], [1, 11, 3]⟩, ⟨1678, false,
    false, [457], [1, 11, 3]⟩, ⟨312, true, false, [], [1317, 1, 11, 3]⟩, ⟨1499, false, false,
    [459], [11, 3]⟩, ⟨1494, false, false, [459], [3]⟩, ⟨1490, false, false, [459], []⟩, ⟨1834,
    false, false, [459], []⟩, ⟨313, true, false, [], [1309]⟩]⟩
,
  ⟨[1309, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11,
    3, 17, 13, 5, 15, 1], [467, 1301], .contexts [⟨2041, false, false, [], [17, 13, 5, 15, 1]⟩,
    ⟨1486, false, false, [461], [13, 5, 15, 1]⟩, ⟨1834, false, false, [461], [13, 5, 15, 1]⟩,
    ⟨314, true, false, [], [1309, 13, 5, 15, 1]⟩, ⟨1478, false, false, [463], [5, 15, 1]⟩,
    ⟨1950, false, false, [463], [5, 15, 1]⟩, ⟨315, true, false, [], [1305, 5, 15, 1]⟩, ⟨1467,
    false, false, [465], [15, 1]⟩, ⟨1950, false, false, [465], [15, 1]⟩, ⟨316, true, false, [],
    [1305, 15, 1]⟩, ⟨1459, false, false, [467], [1]⟩, ⟨1451, false, false, [467], []⟩]⟩
,
  ⟨[1309, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17,
    13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5, 15, 1, 11,
    3, 17, 13, 5, 15, 1, 11, 3, 17, 13, 5], [475, 1291], .contexts [⟨2042, false, false, [],
    [11, 3, 17, 13, 5]⟩, ⟨1442, false, false, [467], [3, 17, 13, 5]⟩, ⟨1985, false, false,
    [467], [3, 17, 13, 5]⟩, ⟨317, true, false, [], [1297, 3, 17, 13, 5]⟩, ⟨1431, false, false,
    [469], [17, 13, 5]⟩, ⟨1985, false, false, [469], [17, 13, 5]⟩, ⟨318, true, false, [], [1297,
    17, 13, 5]⟩, ⟨1422, false, false, [471], [13, 5]⟩, ⟨1413, false, false, [471], [5]⟩, ⟨1877,
    false, false, [471], [5]⟩, ⟨319, true, false, [], [1291, 5]⟩, ⟨1402, false, false, [473],
    []⟩, ⟨1877, false, false, [473], []⟩, ⟨320, true, false, [], [1291]⟩]⟩
,
  ⟨[1339, 19], [1339, 19], .contexts []⟩
,
  ⟨[477], [477], .contexts [⟨877, false, false, [], [477]⟩]⟩
,
  ⟨[1339, 13], [1341], .contexts [⟨322, true, false, [], []⟩]⟩
,
  ⟨[1341, 13], [1339], .contexts [⟨2046, true, false, [], [13]⟩, ⟨18, false, false, [1339], []⟩,
    ⟨2006, false, false, [], []⟩]⟩
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
