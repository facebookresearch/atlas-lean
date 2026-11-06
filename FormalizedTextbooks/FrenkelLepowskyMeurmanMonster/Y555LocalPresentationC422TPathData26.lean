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
def y422TPathRawData26 : Fin 128 → ℕ × ℕ :=
  ![(3327, 3),
    (3328, 0),
    (3329, 1),
    (3330, 5),
    (3331, 7),
    (3332, 2),
    (3333, 6),
    (3334, 3),
    (3335, 0),
    (3336, 1),
    (3337, 5),
    (3338, 7),
    (3339, 2),
    (3340, 6),
    (3341, 3),
    (3342, 0),
    (3343, 1),
    (3344, 5),
    (3345, 7),
    (3346, 2),
    (3347, 6),
    (3348, 3),
    (3349, 4),
    (3350, 0),
    (3351, 1),
    (3352, 5),
    (3353, 7),
    (3354, 2),
    (3355, 6),
    (3356, 3),
    (3357, 0),
    (3358, 1),
    (3359, 5),
    (3360, 7),
    (3361, 2),
    (3362, 6),
    (3363, 3),
    (3364, 0),
    (3365, 1),
    (3366, 5),
    (3367, 7),
    (3368, 2),
    (3369, 6),
    (3370, 3),
    (3371, 0),
    (3372, 1),
    (3373, 5),
    (3374, 7),
    (3375, 2),
    (3376, 6),
    (3377, 3),
    (3378, 0),
    (3379, 1),
    (3380, 5),
    (3381, 7),
    (3382, 2),
    (3383, 6),
    (3384, 3),
    (3385, 0),
    (3386, 1),
    (3387, 5),
    (3388, 7),
    (3389, 2),
    (3390, 6),
    (3391, 3),
    (3392, 0),
    (3393, 1),
    (3394, 5),
    (3395, 7),
    (3396, 2),
    (3397, 6),
    (3398, 3),
    (3399, 0),
    (3400, 1),
    (3401, 5),
    (3402, 7),
    (3403, 2),
    (3404, 6),
    (3405, 3),
    (3406, 0),
    (3407, 1),
    (3408, 5),
    (3409, 7),
    (3410, 2),
    (3411, 6),
    (3412, 3),
    (3413, 4),
    (3414, 0),
    (3415, 1),
    (3416, 5),
    (3417, 7),
    (3418, 2),
    (3419, 6),
    (3420, 3),
    (3421, 0),
    (3422, 1),
    (3423, 5),
    (3424, 7),
    (3425, 2),
    (3426, 6),
    (3427, 3),
    (3428, 0),
    (3429, 1),
    (3430, 5),
    (3431, 7),
    (3432, 2),
    (3433, 6),
    (3434, 3),
    (3435, 0),
    (3436, 1),
    (3437, 5),
    (3438, 7),
    (3439, 2),
    (3440, 6),
    (3441, 3),
    (3442, 0),
    (3443, 1),
    (3444, 5),
    (3445, 7),
    (3446, 2),
    (3447, 6),
    (3448, 3),
    (3449, 0),
    (3450, 1),
    (3451, 5),
    (3452, 7),
    (3453, 2),
    (3454, 6)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData26_allowed (j : Fin 128) :
    (3328 + j.val = 0 ∨ (y422TPathRawData26 j).1 < 3328 + j.val) ∧
      (y422TPathRawData26 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
