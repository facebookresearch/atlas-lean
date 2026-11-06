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
def y422TPathRawData27 : Fin 128 → ℕ × ℕ :=
  ![(3455, 3),
    (3456, 0),
    (3457, 1),
    (3458, 5),
    (3459, 7),
    (3460, 2),
    (2353, 6),
    (3462, 0),
    (3463, 7),
    (3464, 8),
    (3465, 0),
    (3466, 1),
    (3467, 2),
    (3468, 5),
    (3469, 6),
    (3470, 0),
    (3471, 7),
    (3472, 8),
    (3473, 1),
    (3474, 2),
    (3475, 0),
    (3476, 5),
    (3477, 6),
    (3478, 0),
    (3479, 7),
    (3480, 8),
    (3481, 0),
    (3482, 1),
    (3483, 2),
    (3484, 0),
    (3485, 5),
    (3486, 6),
    (3487, 0),
    (3488, 7),
    (3489, 8),
    (3490, 0),
    (3491, 1),
    (3492, 2),
    (3493, 0),
    (3494, 5),
    (3495, 6),
    (3496, 0),
    (3497, 7),
    (3498, 8),
    (3499, 0),
    (3500, 1),
    (3501, 2),
    (3502, 0),
    (3503, 5),
    (3504, 6),
    (3505, 0),
    (3506, 7),
    (3507, 8),
    (3508, 0),
    (2932, 3),
    (3510, 1),
    (3511, 5),
    (3453, 1),
    (3450, 2),
    (3514, 6),
    (3515, 3),
    (3516, 0),
    (3517, 1),
    (3518, 5),
    (3519, 7),
    (3520, 2),
    (3521, 6),
    (3522, 3),
    (3523, 0),
    (3524, 1),
    (3525, 5),
    (3526, 7),
    (3527, 2),
    (3528, 6),
    (3529, 3),
    (3530, 0),
    (3531, 1),
    (3532, 5),
    (3533, 7),
    (3534, 2),
    (3535, 6),
    (3536, 3),
    (3537, 0),
    (3538, 1),
    (3539, 5),
    (3540, 7),
    (3541, 2),
    (3542, 6),
    (3543, 3),
    (3544, 0),
    (3545, 1),
    (3546, 5),
    (3547, 7),
    (3548, 2),
    (3549, 6),
    (3550, 3),
    (3551, 4),
    (3552, 0),
    (3553, 1),
    (3554, 5),
    (3555, 7),
    (3556, 2),
    (3557, 6),
    (3558, 3),
    (3559, 0),
    (3560, 1),
    (3561, 5),
    (3562, 7),
    (3563, 2),
    (3564, 6),
    (3565, 3),
    (3566, 0),
    (3567, 1),
    (3568, 5),
    (3569, 7),
    (3570, 2),
    (3571, 6),
    (3572, 3),
    (3573, 0),
    (3574, 1),
    (3575, 5),
    (3576, 7),
    (3577, 2),
    (3578, 6),
    (3579, 3),
    (3580, 0),
    (3581, 1),
    (3582, 5)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData27_allowed (j : Fin 128) :
    (3456 + j.val = 0 ∨ (y422TPathRawData27 j).1 < 3456 + j.val) ∧
      (y422TPathRawData27 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
