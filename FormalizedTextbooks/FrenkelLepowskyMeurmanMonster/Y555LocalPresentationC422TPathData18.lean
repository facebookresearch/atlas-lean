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
def y422TPathRawData18 : Fin 128 → ℕ × ℕ :=
  ![(2303, 6),
    (2304, 0),
    (2305, 7),
    (2306, 8),
    (2307, 0),
    (2308, 1),
    (2309, 2),
    (2310, 0),
    (2311, 5),
    (2312, 6),
    (2313, 0),
    (2314, 7),
    (2315, 8),
    (2316, 0),
    (2317, 1),
    (2318, 2),
    (2319, 0),
    (2320, 5),
    (2321, 6),
    (2322, 0),
    (2323, 7),
    (2324, 8),
    (2325, 0),
    (2326, 1),
    (2327, 2),
    (2328, 0),
    (2329, 5),
    (2330, 6),
    (2331, 0),
    (2332, 7),
    (2333, 8),
    (2334, 0),
    (2335, 1),
    (2336, 2),
    (2337, 0),
    (2338, 5),
    (2339, 6),
    (2340, 0),
    (2341, 7),
    (2342, 8),
    (2343, 0),
    (2344, 1),
    (2345, 2),
    (2346, 0),
    (2347, 5),
    (2348, 6),
    (2349, 0),
    (2350, 7),
    (2351, 8),
    (2352, 0),
    (661, 7),
    (2354, 0),
    (2355, 1),
    (2356, 2),
    (2357, 5),
    (801, 7),
    (2359, 8),
    (2360, 1),
    (2361, 2),
    (2362, 0),
    (2363, 5),
    (2364, 6),
    (2365, 0),
    (2366, 7),
    (2367, 8),
    (2368, 0),
    (2369, 1),
    (2370, 2),
    (2371, 0),
    (2372, 5),
    (2373, 6),
    (2374, 0),
    (2375, 7),
    (2376, 8),
    (2377, 0),
    (2378, 1),
    (2379, 2),
    (2380, 0),
    (2381, 5),
    (2382, 6),
    (2383, 0),
    (2384, 7),
    (2385, 8),
    (2386, 0),
    (2387, 1),
    (2388, 2),
    (2389, 0),
    (2390, 5),
    (2391, 6),
    (2392, 0),
    (2393, 7),
    (2394, 8),
    (2395, 0),
    (2396, 1),
    (2397, 2),
    (2398, 0),
    (2399, 5),
    (2400, 6),
    (2401, 0),
    (2402, 7),
    (2403, 8),
    (2404, 0),
    (2405, 1),
    (2406, 2),
    (2407, 0),
    (2408, 5),
    (2409, 6),
    (2410, 0),
    (2411, 7),
    (2412, 8),
    (2413, 0),
    (2414, 1),
    (2415, 2),
    (2416, 0),
    (791, 7),
    (2418, 0),
    (2419, 1),
    (709, 6),
    (2421, 0),
    (704, 8),
    (2423, 5),
    (2424, 0),
    (2425, 7),
    (2426, 8),
    (2427, 1),
    (2428, 2),
    (2429, 0),
    (2430, 5)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData18_allowed (j : Fin 128) :
    (2304 + j.val = 0 ∨ (y422TPathRawData18 j).1 < 2304 + j.val) ∧
      (y422TPathRawData18 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
