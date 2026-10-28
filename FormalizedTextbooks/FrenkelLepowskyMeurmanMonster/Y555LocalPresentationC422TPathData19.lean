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
def y422TPathRawData19 : Fin 128 → ℕ × ℕ :=
  ![(2431, 6),
    (2432, 7),
    (2433, 8),
    (2434, 0),
    (2435, 1),
    (2436, 2),
    (2437, 0),
    (2438, 5),
    (2439, 6),
    (2440, 0),
    (2441, 7),
    (2442, 8),
    (2443, 0),
    (2444, 1),
    (2445, 2),
    (2446, 0),
    (2447, 5),
    (2448, 6),
    (2449, 0),
    (2450, 7),
    (2451, 8),
    (2452, 0),
    (2453, 1),
    (2454, 2),
    (2455, 0),
    (2456, 5),
    (2457, 6),
    (2458, 0),
    (2459, 7),
    (2460, 8),
    (2461, 0),
    (2462, 1),
    (2463, 2),
    (2464, 0),
    (2465, 5),
    (2466, 6),
    (2467, 0),
    (2468, 7),
    (2469, 8),
    (2470, 0),
    (647, 7),
    (794, 1),
    (109, 5),
    (2474, 6),
    (2475, 0),
    (2476, 7),
    (2477, 8),
    (2478, 1),
    (2479, 2),
    (2480, 0),
    (2481, 5),
    (2482, 6),
    (2483, 0),
    (2484, 7),
    (2485, 8),
    (2486, 0),
    (2487, 1),
    (2488, 2),
    (2489, 0),
    (2490, 5),
    (2491, 6),
    (2492, 0),
    (2493, 7),
    (2494, 8),
    (2495, 0),
    (2496, 1),
    (2497, 2),
    (2498, 0),
    (2499, 5),
    (2500, 6),
    (2501, 0),
    (2502, 7),
    (2503, 8),
    (2504, 0),
    (2505, 1),
    (2506, 2),
    (2507, 0),
    (2508, 5),
    (2509, 6),
    (2510, 0),
    (2511, 7),
    (2512, 8),
    (2513, 0),
    (2514, 1),
    (2515, 2),
    (2516, 0),
    (2517, 5),
    (2518, 6),
    (2519, 0),
    (2520, 7),
    (2521, 8),
    (2522, 0),
    (2523, 1),
    (2524, 2),
    (2525, 0),
    (2526, 5),
    (2527, 6),
    (2528, 0),
    (2529, 7),
    (2530, 8),
    (2531, 0),
    (2532, 1),
    (2533, 2),
    (2534, 0),
    (2535, 5),
    (2536, 6),
    (300, 1),
    (843, 6),
    (2539, 0),
    (838, 8),
    (2541, 1),
    (2542, 2),
    (2543, 0),
    (2544, 5),
    (2545, 6),
    (2546, 0),
    (2547, 7),
    (2548, 8),
    (2549, 0),
    (2550, 1),
    (2551, 2),
    (2552, 0),
    (2553, 5),
    (2554, 6),
    (2555, 0),
    (2556, 7),
    (2557, 8),
    (2558, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData19_allowed (j : Fin 128) :
    (2432 + j.val = 0 ∨ (y422TPathRawData19 j).1 < 2432 + j.val) ∧
      (y422TPathRawData19 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
