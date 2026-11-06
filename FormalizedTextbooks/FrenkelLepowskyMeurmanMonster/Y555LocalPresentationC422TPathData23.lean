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
def y422TPathRawData23 : Fin 128 → ℕ × ℕ :=
  ![(2943, 0),
    (2944, 1),
    (2945, 2),
    (2946, 0),
    (2947, 5),
    (2948, 6),
    (2949, 0),
    (2950, 7),
    (2951, 8),
    (2952, 0),
    (2953, 1),
    (2954, 2),
    (2955, 0),
    (2956, 5),
    (2957, 6),
    (2958, 0),
    (2959, 7),
    (2960, 8),
    (2961, 0),
    (2962, 1),
    (2963, 2),
    (2964, 0),
    (2965, 5),
    (2966, 6),
    (2967, 0),
    (2968, 7),
    (2969, 8),
    (2970, 0),
    (2971, 1),
    (2972, 2),
    (2973, 0),
    (2974, 5),
    (2975, 6),
    (2976, 0),
    (2977, 7),
    (2978, 8),
    (2979, 0),
    (2587, 3),
    (2981, 0),
    (2982, 1),
    (2983, 5),
    (2984, 7),
    (2985, 2),
    (2986, 6),
    (2987, 3),
    (2988, 0),
    (2989, 1),
    (2990, 5),
    (2991, 7),
    (2992, 2),
    (2993, 6),
    (2994, 3),
    (2995, 0),
    (2996, 1),
    (2997, 5),
    (2998, 7),
    (2999, 2),
    (3000, 6),
    (3001, 3),
    (3002, 0),
    (3003, 1),
    (3004, 5),
    (3005, 7),
    (3006, 2),
    (3007, 6),
    (3008, 3),
    (3009, 0),
    (3010, 1),
    (3011, 5),
    (3012, 7),
    (3013, 2),
    (3014, 6),
    (3015, 3),
    (3016, 0),
    (3017, 1),
    (3018, 5),
    (3019, 7),
    (3020, 2),
    (3021, 6),
    (3022, 3),
    (3023, 0),
    (3024, 1),
    (3025, 5),
    (3026, 7),
    (3027, 2),
    (3028, 6),
    (3029, 3),
    (3030, 4),
    (3031, 0),
    (3032, 1),
    (3033, 5),
    (3034, 7),
    (3035, 2),
    (3036, 6),
    (3037, 3),
    (3038, 0),
    (3039, 1),
    (3040, 5),
    (3041, 7),
    (3042, 2),
    (3043, 6),
    (3044, 3),
    (3045, 0),
    (3046, 1),
    (3047, 5),
    (3048, 7),
    (3049, 2),
    (3050, 6),
    (3051, 3),
    (3052, 0),
    (3053, 1),
    (3054, 5),
    (3055, 7),
    (3056, 2),
    (3057, 6),
    (3058, 3),
    (3059, 0),
    (3060, 1),
    (3061, 5),
    (3062, 7),
    (3063, 2),
    (3064, 6),
    (3065, 3),
    (3066, 0),
    (3067, 1),
    (3068, 5),
    (3069, 7),
    (3070, 2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData23_allowed (j : Fin 128) :
    (2944 + j.val = 0 ∨ (y422TPathRawData23 j).1 < 2944 + j.val) ∧
      (y422TPathRawData23 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
