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
def y422TPathRawData16 : Fin 128 → ℕ × ℕ :=
  ![(2047, 2),
    (2048, 0),
    (2049, 5),
    (2050, 6),
    (2051, 0),
    (2052, 7),
    (2053, 8),
    (2054, 0),
    (2055, 1),
    (2056, 2),
    (2057, 0),
    (2058, 5),
    (2059, 6),
    (2060, 0),
    (2061, 7),
    (2062, 8),
    (2063, 0),
    (2064, 1),
    (2065, 2),
    (2066, 0),
    (2067, 5),
    (2068, 6),
    (2069, 0),
    (2070, 7),
    (2071, 8),
    (2072, 0),
    (2073, 1),
    (2074, 2),
    (2075, 0),
    (2076, 5),
    (2077, 6),
    (2078, 0),
    (2079, 7),
    (2080, 8),
    (2081, 0),
    (2082, 1),
    (2083, 2),
    (2084, 0),
    (2085, 5),
    (2086, 6),
    (2087, 0),
    (2088, 7),
    (2089, 8),
    (2090, 0),
    (2091, 1),
    (2092, 2),
    (2093, 0),
    (2094, 5),
    (362, 8),
    (1063, 7),
    (2097, 0),
    (2098, 1),
    (2099, 2),
    (2100, 5),
    (2101, 6),
    (2102, 0),
    (2103, 7),
    (2104, 8),
    (2105, 1),
    (2106, 2),
    (2107, 0),
    (2108, 5),
    (2109, 6),
    (2110, 0),
    (2111, 7),
    (2112, 8),
    (2113, 0),
    (2114, 1),
    (2115, 2),
    (2116, 0),
    (2117, 5),
    (2118, 6),
    (2119, 0),
    (2120, 7),
    (2121, 8),
    (2122, 0),
    (2123, 1),
    (2124, 2),
    (2125, 0),
    (2126, 5),
    (2127, 6),
    (2128, 0),
    (2129, 7),
    (2130, 8),
    (2131, 0),
    (2132, 1),
    (2133, 2),
    (2134, 0),
    (2135, 5),
    (2136, 6),
    (2137, 0),
    (2138, 7),
    (2139, 8),
    (2140, 0),
    (2141, 1),
    (2142, 2),
    (2143, 0),
    (2144, 5),
    (2145, 6),
    (2146, 0),
    (2147, 7),
    (2148, 8),
    (2149, 0),
    (2150, 1),
    (2151, 2),
    (2152, 0),
    (2153, 5),
    (2154, 6),
    (2155, 0),
    (2156, 7),
    (2157, 8),
    (2158, 0),
    (255, 8),
    (2095, 1),
    (2161, 2),
    (2162, 5),
    (2163, 6),
    (2164, 0),
    (2165, 7),
    (2166, 8),
    (2167, 1),
    (2168, 2),
    (2169, 0),
    (2170, 5),
    (2171, 6),
    (2172, 0),
    (2173, 7),
    (2174, 8)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData16_allowed (j : Fin 128) :
    (2048 + j.val = 0 ∨ (y422TPathRawData16 j).1 < 2048 + j.val) ∧
      (y422TPathRawData16 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
