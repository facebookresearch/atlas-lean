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
def y422TPathRawData22 : Fin 128 → ℕ × ℕ :=
  ![(2815, 7),
    (2816, 2),
    (2817, 6),
    (2818, 3),
    (2819, 4),
    (2820, 0),
    (2821, 1),
    (2822, 5),
    (2823, 7),
    (2824, 2),
    (2825, 6),
    (2826, 3),
    (2827, 0),
    (2828, 1),
    (2829, 5),
    (2830, 7),
    (2831, 2),
    (2832, 6),
    (2833, 3),
    (2834, 0),
    (2835, 1),
    (2836, 5),
    (2837, 7),
    (2838, 2),
    (2839, 6),
    (2840, 3),
    (2841, 0),
    (2842, 1),
    (2843, 5),
    (2844, 7),
    (2845, 2),
    (2846, 6),
    (2847, 3),
    (2848, 0),
    (2849, 1),
    (2850, 5),
    (2851, 7),
    (2852, 2),
    (2853, 6),
    (2854, 3),
    (2855, 0),
    (2856, 1),
    (2857, 5),
    (2858, 7),
    (2859, 2),
    (2860, 6),
    (2861, 3),
    (2862, 0),
    (2863, 1),
    (2864, 5),
    (2865, 7),
    (2866, 2),
    (2867, 6),
    (2868, 3),
    (2869, 0),
    (2870, 1),
    (2871, 5),
    (2872, 7),
    (2873, 2),
    (2874, 6),
    (2875, 3),
    (2876, 0),
    (2877, 1),
    (2878, 5),
    (2879, 7),
    (2880, 2),
    (2881, 6),
    (2882, 3),
    (2883, 4),
    (2884, 0),
    (2885, 1),
    (2886, 5),
    (2887, 7),
    (2888, 2),
    (2889, 6),
    (2890, 3),
    (2891, 0),
    (2892, 1),
    (2893, 5),
    (2894, 7),
    (2895, 2),
    (2896, 6),
    (2897, 3),
    (2898, 0),
    (2899, 1),
    (2900, 5),
    (2901, 7),
    (2902, 2),
    (2903, 6),
    (2904, 3),
    (2905, 0),
    (2906, 1),
    (2907, 5),
    (2908, 7),
    (2909, 2),
    (2910, 6),
    (2911, 3),
    (2912, 0),
    (2913, 1),
    (2914, 5),
    (2915, 7),
    (2916, 2),
    (2917, 6),
    (2918, 3),
    (2919, 0),
    (2920, 1),
    (2921, 5),
    (2922, 7),
    (2923, 2),
    (2924, 6),
    (2925, 3),
    (2926, 0),
    (2927, 1),
    (2928, 5),
    (2929, 7),
    (2930, 2),
    (710, 6),
    (2422, 5),
    (2933, 0),
    (837, 8),
    (2935, 0),
    (2936, 1),
    (2937, 2),
    (2938, 0),
    (2939, 5),
    (2940, 6),
    (2941, 7),
    (2942, 8)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData22_allowed (j : Fin 128) :
    (2816 + j.val = 0 ∨ (y422TPathRawData22 j).1 < 2816 + j.val) ∧
      (y422TPathRawData22 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
