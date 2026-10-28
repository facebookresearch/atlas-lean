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
def y422TPathRawData28 : Fin 128 → ℕ × ℕ :=
  ![(3583, 7),
    (3584, 2),
    (3585, 6),
    (3586, 3),
    (3587, 0),
    (3588, 1),
    (3589, 5),
    (3590, 7),
    (3591, 2),
    (3592, 6),
    (3593, 3),
    (3594, 0),
    (3595, 1),
    (3596, 5),
    (3597, 7),
    (3598, 2),
    (3599, 6),
    (3600, 3),
    (3601, 0),
    (3602, 1),
    (3603, 5),
    (3604, 7),
    (3605, 2),
    (3606, 6),
    (3607, 3),
    (3608, 0),
    (3609, 1),
    (3610, 5),
    (3611, 7),
    (3612, 2),
    (3613, 6),
    (3614, 3),
    (3615, 4),
    (3616, 0),
    (3617, 1),
    (3618, 5),
    (3619, 7),
    (3620, 2),
    (3621, 6),
    (3622, 3),
    (3623, 0),
    (3624, 1),
    (3625, 5),
    (3626, 7),
    (3627, 2),
    (3628, 6),
    (3629, 3),
    (3630, 0),
    (3631, 1),
    (3632, 5),
    (3633, 7),
    (3634, 2),
    (3635, 6),
    (3636, 3),
    (3637, 0),
    (3638, 1),
    (3639, 5),
    (3640, 7),
    (3641, 2),
    (3642, 6),
    (3643, 3),
    (3644, 0),
    (3645, 1),
    (3646, 5),
    (3647, 7),
    (3648, 2),
    (3649, 6),
    (3650, 3),
    (3651, 0),
    (3652, 1),
    (3653, 5),
    (3654, 7),
    (3655, 2),
    (3656, 6),
    (3657, 3),
    (3658, 0),
    (3659, 1),
    (3660, 5),
    (3661, 7),
    (3662, 2),
    (986, 4),
    (768, 2),
    (3665, 0),
    (3666, 5),
    (3667, 6),
    (3668, 0),
    (3669, 7),
    (3670, 8),
    (3671, 1),
    (3672, 0),
    (3673, 5),
    (3674, 6),
    (3675, 0),
    (3676, 7),
    (3677, 8),
    (3678, 0),
    (3679, 1),
    (3680, 2),
    (3681, 0),
    (3682, 5),
    (3683, 6),
    (3684, 0),
    (3685, 7),
    (3686, 8),
    (3687, 0),
    (3688, 1),
    (3689, 2),
    (3690, 0),
    (3691, 5),
    (3692, 6),
    (3693, 0),
    (3694, 7),
    (3695, 8),
    (3696, 0),
    (3697, 1),
    (3698, 2),
    (3699, 0),
    (3700, 5),
    (3701, 6),
    (3702, 0),
    (3703, 7),
    (3704, 8),
    (3705, 0),
    (3706, 1),
    (3707, 2),
    (3708, 0),
    (3709, 5),
    (3710, 6)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData28_allowed (j : Fin 128) :
    (3584 + j.val = 0 ∨ (y422TPathRawData28 j).1 < 3584 + j.val) ∧
      (y422TPathRawData28 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
