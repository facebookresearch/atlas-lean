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
def y422TPathRawData17 : Fin 128 → ℕ × ℕ :=
  ![(2175, 0),
    (2176, 1),
    (2177, 2),
    (2178, 0),
    (2179, 5),
    (2180, 6),
    (2181, 0),
    (2182, 7),
    (2183, 8),
    (2184, 0),
    (2185, 1),
    (2186, 2),
    (2187, 0),
    (2188, 5),
    (2189, 6),
    (2190, 0),
    (2191, 7),
    (2192, 8),
    (2193, 0),
    (2194, 1),
    (2195, 2),
    (2196, 0),
    (2197, 5),
    (2198, 6),
    (2199, 0),
    (2200, 7),
    (2201, 8),
    (2202, 0),
    (2203, 1),
    (2204, 2),
    (2205, 0),
    (2206, 5),
    (2207, 6),
    (2208, 0),
    (2209, 7),
    (2210, 8),
    (2211, 0),
    (2212, 1),
    (2213, 2),
    (2214, 0),
    (2215, 5),
    (2216, 6),
    (2217, 0),
    (2218, 7),
    (2219, 8),
    (2220, 0),
    (2221, 1),
    (2222, 2),
    (2223, 0),
    (2224, 5),
    (653, 8),
    (980, 1),
    (2227, 2),
    (2228, 5),
    (2229, 6),
    (2230, 0),
    (2231, 7),
    (1835, 1),
    (2233, 2),
    (2234, 0),
    (2235, 5),
    (2236, 6),
    (2237, 0),
    (2238, 7),
    (2239, 8),
    (2240, 0),
    (2241, 1),
    (2242, 2),
    (2243, 0),
    (2244, 5),
    (2245, 6),
    (2246, 0),
    (2247, 7),
    (2248, 8),
    (2249, 0),
    (2250, 1),
    (2251, 2),
    (2252, 0),
    (2253, 5),
    (2254, 6),
    (2255, 0),
    (2256, 7),
    (2257, 8),
    (2258, 0),
    (2259, 1),
    (2260, 2),
    (2261, 0),
    (2262, 5),
    (2263, 6),
    (2264, 0),
    (2265, 7),
    (2266, 8),
    (2267, 0),
    (2268, 1),
    (2269, 2),
    (2270, 0),
    (2271, 5),
    (2272, 6),
    (2273, 0),
    (2274, 7),
    (2275, 8),
    (2276, 0),
    (2277, 1),
    (2278, 2),
    (2279, 0),
    (2280, 5),
    (2281, 6),
    (2282, 0),
    (2283, 7),
    (2284, 8),
    (2285, 0),
    (2286, 1),
    (2287, 2),
    (2288, 0),
    (1058, 7),
    (659, 2),
    (345, 1),
    (2292, 2),
    (2293, 5),
    (2294, 6),
    (2295, 0),
    (2296, 7),
    (2297, 8),
    (2298, 0),
    (2299, 1),
    (2300, 2),
    (2301, 0),
    (2302, 5)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData17_allowed (j : Fin 128) :
    (2176 + j.val = 0 ∨ (y422TPathRawData17 j).1 < 2176 + j.val) ∧
      (y422TPathRawData17 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
