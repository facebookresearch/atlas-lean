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
def y422TPathRawData21 : Fin 128 → ℕ × ℕ :=
  ![(2687, 3),
    (2688, 0),
    (2689, 1),
    (2690, 5),
    (2691, 7),
    (2692, 2),
    (2693, 6),
    (2694, 3),
    (2695, 0),
    (2696, 1),
    (2697, 5),
    (2698, 7),
    (2699, 2),
    (2700, 6),
    (2701, 3),
    (2702, 0),
    (2703, 1),
    (2704, 5),
    (2705, 7),
    (2706, 2),
    (2707, 6),
    (2708, 3),
    (2709, 0),
    (2710, 1),
    (2711, 5),
    (2712, 7),
    (2713, 2),
    (2714, 6),
    (2715, 3),
    (2716, 0),
    (2717, 1),
    (2718, 5),
    (2719, 7),
    (2720, 2),
    (2721, 6),
    (2722, 3),
    (2723, 0),
    (2724, 1),
    (2725, 5),
    (2726, 7),
    (2727, 2),
    (2728, 6),
    (2729, 3),
    (2730, 0),
    (2731, 1),
    (2732, 5),
    (2733, 7),
    (2734, 2),
    (2735, 6),
    (2736, 3),
    (2737, 0),
    (2738, 1),
    (2739, 5),
    (2740, 7),
    (2741, 2),
    (2742, 6),
    (2743, 3),
    (2744, 4),
    (2745, 0),
    (2746, 1),
    (2747, 5),
    (2748, 7),
    (2749, 2),
    (2750, 6),
    (2751, 3),
    (2752, 0),
    (2753, 1),
    (2754, 5),
    (2755, 7),
    (2756, 2),
    (2757, 6),
    (2758, 3),
    (2759, 0),
    (2760, 1),
    (2761, 5),
    (2762, 7),
    (2763, 2),
    (2764, 6),
    (2765, 3),
    (2766, 0),
    (2767, 1),
    (2768, 5),
    (2769, 7),
    (2770, 2),
    (2771, 6),
    (2772, 3),
    (2773, 0),
    (2774, 1),
    (2775, 5),
    (2776, 7),
    (2777, 2),
    (1070, 1),
    (2779, 5),
    (2780, 7),
    (2781, 2),
    (2782, 6),
    (2783, 3),
    (2784, 0),
    (2785, 1),
    (2786, 5),
    (2787, 7),
    (2788, 2),
    (2789, 6),
    (2790, 3),
    (2791, 0),
    (2792, 1),
    (2793, 5),
    (2794, 7),
    (2795, 2),
    (2796, 6),
    (2797, 3),
    (2798, 0),
    (2799, 1),
    (2800, 5),
    (2801, 7),
    (2802, 2),
    (2803, 6),
    (2804, 3),
    (2805, 0),
    (2806, 1),
    (2807, 5),
    (2808, 7),
    (2809, 2),
    (2810, 6),
    (2811, 3),
    (2812, 0),
    (2813, 1),
    (2814, 5)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData21_allowed (j : Fin 128) :
    (2688 + j.val = 0 ∨ (y422TPathRawData21 j).1 < 2688 + j.val) ∧
      (y422TPathRawData21 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
