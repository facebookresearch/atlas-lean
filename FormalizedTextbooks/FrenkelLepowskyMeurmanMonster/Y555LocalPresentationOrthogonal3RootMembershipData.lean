/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal natural coordinate codes of the actual E7 source roots. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3VectorCode

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- Exact natural coordinate labels of the 126 actual source root vectors. -/
def y322Orthogonal3E7RootCode : Fin 126 → ℕ :=
![
  1, 2, 4, 82, 730, 8, 164, 1460, 3, 13, 85, 733, 81, 325, 811, 729, 6, 26, 170, 1466, 162, 650,
  1622, 1458, 12, 40, 94, 742, 328, 814, 324, 1054, 24, 80, 188, 1484, 656, 1628, 648, 2108, 9,
  39, 121, 769, 337, 823, 1057, 815, 243, 18, 78, 242, 1538, 674, 1646, 2114, 1627, 486, 36,
  364, 850, 1066, 824, 1058, 72, 728, 1700, 2132, 1645, 2113, 27, 1093, 851, 1067, 827, 1139,
  54, 2186, 1699, 2131, 1642, 2032, 1094, 854, 1070, 1148, 2185, 1696, 2128, 2050, 1097, 1175,
  863, 1151, 2182, 2104, 1687, 2047, 1106, 1178, 1149, 2173, 2101, 2046, 1187, 1176, 1878, 2092,
  2100, 1317, 1185, 1905, 2091, 1371, 1179, 1914, 2088, 1362, 1908, 1359, 1909, 1361, 1747,
  1280, 1990, 1037]

/-- A literal list of exact source root labels for bounded finite membership evaluation. -/
def y322Orthogonal3E7RootCodeList : List ℕ :=
[
  1, 2, 4, 82, 730, 8, 164, 1460, 3, 13, 85, 733, 81, 325, 811, 729, 6, 26, 170, 1466, 162, 650,
  1622, 1458, 12, 40, 94, 742, 328, 814, 324, 1054, 24, 80, 188, 1484, 656, 1628, 648, 2108, 9,
  39, 121, 769, 337, 823, 1057, 815, 243, 18, 78, 242, 1538, 674, 1646, 2114, 1627, 486, 36,
  364, 850, 1066, 824, 1058, 72, 728, 1700, 2132, 1645, 2113, 27, 1093, 851, 1067, 827, 1139,
  54, 2186, 1699, 2131, 1642, 2032, 1094, 854, 1070, 1148, 2185, 1696, 2128, 2050, 1097, 1175,
  863, 1151, 2182, 2104, 1687, 2047, 1106, 1178, 1149, 2173, 2101, 2046, 1187, 1176, 1878, 2092,
  2100, 1317, 1185, 1905, 2091, 1371, 1179, 1914, 2088, 1362, 1908, 1359, 1909, 1361, 1747,
  1280, 1990, 1037]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
