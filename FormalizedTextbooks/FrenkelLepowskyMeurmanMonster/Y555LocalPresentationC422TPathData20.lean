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
def y422TPathRawData20 : Fin 128 → ℕ × ℕ :=
  ![(2559, 1),
    (2560, 2),
    (2561, 0),
    (2562, 5),
    (2563, 6),
    (2564, 0),
    (2565, 7),
    (2566, 8),
    (2567, 0),
    (2568, 1),
    (2569, 2),
    (2570, 0),
    (2571, 5),
    (2572, 6),
    (2573, 0),
    (2574, 7),
    (2575, 8),
    (2576, 0),
    (2577, 1),
    (2578, 2),
    (2579, 0),
    (2580, 5),
    (2581, 6),
    (2582, 0),
    (2583, 7),
    (2584, 8),
    (2585, 0),
    (2586, 2),
    (2587, 0),
    (2588, 5),
    (2589, 6),
    (589, 1),
    (2403, 5),
    (2592, 6),
    (2593, 0),
    (2594, 7),
    (2595, 8),
    (2596, 0),
    (2597, 1),
    (2598, 2),
    (2599, 0),
    (2600, 5),
    (2601, 6),
    (2602, 0),
    (2603, 7),
    (2604, 8),
    (2605, 0),
    (2606, 1),
    (2607, 2),
    (2608, 0),
    (2609, 5),
    (2610, 6),
    (2611, 0),
    (2612, 7),
    (2613, 8),
    (2614, 0),
    (2615, 1),
    (2616, 2),
    (2617, 0),
    (2618, 5),
    (2619, 6),
    (2620, 0),
    (2621, 7),
    (2622, 8),
    (2623, 0),
    (2624, 1),
    (2625, 2),
    (2626, 0),
    (2627, 5),
    (2628, 6),
    (2227, 5),
    (1832, 3),
    (2631, 0),
    (2632, 1),
    (2633, 5),
    (2634, 7),
    (2635, 2),
    (2636, 6),
    (2637, 3),
    (2638, 0),
    (2639, 1),
    (2640, 5),
    (2641, 7),
    (2642, 2),
    (2643, 6),
    (2644, 3),
    (2645, 0),
    (2646, 1),
    (2647, 5),
    (2648, 7),
    (2649, 2),
    (2650, 6),
    (2651, 3),
    (2652, 0),
    (2653, 1),
    (2654, 5),
    (2655, 7),
    (2656, 2),
    (2657, 6),
    (2658, 3),
    (2659, 0),
    (2660, 1),
    (2661, 5),
    (2662, 7),
    (2663, 2),
    (2664, 6),
    (2665, 3),
    (2666, 0),
    (2667, 1),
    (2668, 5),
    (2669, 7),
    (2670, 2),
    (2671, 6),
    (2672, 3),
    (2673, 0),
    (2674, 1),
    (2675, 5),
    (2676, 7),
    (2677, 2),
    (2678, 6),
    (2679, 3),
    (2680, 4),
    (2681, 0),
    (2682, 1),
    (2683, 5),
    (2684, 7),
    (2685, 2),
    (2686, 6)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData20_allowed (j : Fin 128) :
    (2560 + j.val = 0 ∨ (y422TPathRawData20 j).1 < 2560 + j.val) ∧
      (y422TPathRawData20 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
