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
def y422TPathRawData24 : Fin 128 → ℕ × ℕ :=
  ![(3071, 6),
    (3072, 3),
    (3073, 0),
    (3074, 1),
    (3075, 5),
    (3076, 7),
    (3077, 2),
    (3078, 6),
    (3079, 3),
    (3080, 0),
    (3081, 1),
    (3082, 5),
    (3083, 7),
    (3084, 2),
    (3085, 6),
    (3086, 3),
    (3087, 0),
    (3088, 1),
    (3089, 5),
    (3090, 7),
    (3091, 2),
    (3092, 6),
    (3093, 3),
    (3094, 4),
    (3095, 0),
    (3096, 1),
    (3097, 5),
    (3098, 7),
    (3099, 2),
    (3100, 6),
    (3101, 3),
    (3102, 0),
    (3103, 1),
    (3104, 5),
    (3105, 7),
    (3106, 2),
    (3107, 6),
    (3108, 3),
    (3109, 0),
    (3110, 1),
    (3111, 5),
    (3112, 7),
    (3113, 2),
    (3114, 6),
    (3115, 3),
    (3116, 0),
    (3117, 1),
    (3118, 5),
    (3119, 7),
    (3120, 2),
    (3121, 6),
    (3122, 3),
    (3123, 0),
    (3124, 1),
    (3125, 5),
    (3126, 7),
    (3127, 2),
    (3128, 6),
    (3129, 3),
    (3130, 0),
    (3131, 1),
    (3132, 5),
    (3133, 7),
    (3134, 2),
    (3135, 6),
    (3136, 3),
    (3137, 0),
    (904, 4),
    (2295, 3),
    (3140, 0),
    (3141, 1),
    (3142, 5),
    (3143, 2),
    (3144, 0),
    (3145, 1),
    (3146, 5),
    (3147, 7),
    (3148, 2),
    (3149, 6),
    (3150, 3),
    (3151, 0),
    (3152, 1),
    (3153, 5),
    (3154, 7),
    (3155, 2),
    (3156, 6),
    (3157, 3),
    (3158, 0),
    (3159, 1),
    (3160, 5),
    (3161, 7),
    (3162, 2),
    (3163, 6),
    (3164, 3),
    (3165, 0),
    (3166, 1),
    (3167, 5),
    (3168, 7),
    (3169, 2),
    (3170, 6),
    (3171, 3),
    (3172, 0),
    (3173, 1),
    (3174, 5),
    (3175, 7),
    (3176, 2),
    (3177, 6),
    (3178, 3),
    (3179, 0),
    (3180, 1),
    (3181, 5),
    (3182, 7),
    (3183, 2),
    (3184, 6),
    (3185, 3),
    (3186, 4),
    (3187, 0),
    (3188, 1),
    (3189, 5),
    (3190, 7),
    (3191, 2),
    (3192, 6),
    (3193, 3),
    (3194, 0),
    (3195, 1),
    (3196, 5),
    (3197, 7),
    (3198, 2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData24_allowed (j : Fin 128) :
    (3072 + j.val = 0 ∨ (y422TPathRawData24 j).1 < 3072 + j.val) ∧
      (y422TPathRawData24 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
