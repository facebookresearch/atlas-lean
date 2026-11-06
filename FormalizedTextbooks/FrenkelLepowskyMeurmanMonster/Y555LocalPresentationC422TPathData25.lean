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
def y422TPathRawData25 : Fin 128 → ℕ × ℕ :=
  ![(3199, 6),
    (3200, 3),
    (3201, 0),
    (3202, 1),
    (3203, 5),
    (3204, 7),
    (3205, 2),
    (3206, 6),
    (3207, 3),
    (3208, 0),
    (3209, 1),
    (3210, 5),
    (3211, 7),
    (3212, 2),
    (3213, 6),
    (3214, 3),
    (3215, 0),
    (3216, 1),
    (3217, 5),
    (3218, 7),
    (3219, 2),
    (3220, 6),
    (3221, 3),
    (3222, 0),
    (3223, 1),
    (3224, 5),
    (3225, 7),
    (3226, 2),
    (3227, 6),
    (3228, 3),
    (3229, 0),
    (3230, 1),
    (3231, 5),
    (3232, 7),
    (3233, 2),
    (3234, 6),
    (3235, 3),
    (3236, 0),
    (3237, 1),
    (3238, 5),
    (3239, 7),
    (3240, 2),
    (3241, 6),
    (3242, 3),
    (3243, 0),
    (3244, 1),
    (3245, 5),
    (3246, 7),
    (3247, 2),
    (3248, 6),
    (3249, 3),
    (3250, 4),
    (3251, 0),
    (3252, 1),
    (3253, 5),
    (3254, 7),
    (3255, 2),
    (3256, 6),
    (3257, 3),
    (3258, 0),
    (3259, 1),
    (3260, 5),
    (3261, 7),
    (3262, 2),
    (3263, 6),
    (3264, 3),
    (3265, 0),
    (3266, 1),
    (3267, 5),
    (3268, 7),
    (3269, 2),
    (3270, 6),
    (3271, 3),
    (3272, 0),
    (3273, 1),
    (3274, 5),
    (3275, 7),
    (3276, 2),
    (3277, 6),
    (3278, 3),
    (3279, 0),
    (3280, 1),
    (3281, 5),
    (3282, 7),
    (3283, 2),
    (3284, 6),
    (3285, 3),
    (3286, 0),
    (3287, 1),
    (3288, 5),
    (3289, 7),
    (3290, 2),
    (3291, 6),
    (3292, 3),
    (3293, 0),
    (3294, 1),
    (3295, 5),
    (3296, 7),
    (3297, 2),
    (1830, 5),
    (1353, 3),
    (3300, 0),
    (3301, 1),
    (3302, 5),
    (3303, 7),
    (3304, 2),
    (3305, 6),
    (3306, 3),
    (3307, 0),
    (3308, 1),
    (3309, 5),
    (3310, 7),
    (3311, 2),
    (3312, 6),
    (3313, 3),
    (3314, 0),
    (3315, 1),
    (3316, 5),
    (3317, 7),
    (3318, 2),
    (3319, 6),
    (3320, 3),
    (3321, 0),
    (3322, 1),
    (3323, 5),
    (3324, 7),
    (3325, 2),
    (3326, 6)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData25_allowed (j : Fin 128) :
    (3200 + j.val = 0 ∨ (y422TPathRawData25 j).1 < 3200 + j.val) ∧
      (y422TPathRawData25 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
