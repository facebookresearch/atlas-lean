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
def y422TPathRawData29 : Fin 128 → ℕ × ℕ :=
  ![(3711, 0),
    (3712, 7),
    (3713, 8),
    (3714, 0),
    (3715, 1),
    (3716, 2),
    (3717, 0),
    (722, 3),
    (3719, 0),
    (3720, 5),
    (3721, 7),
    (3722, 2),
    (3723, 6),
    (3724, 3),
    (3725, 0),
    (3726, 1),
    (3727, 5),
    (3728, 7),
    (3729, 2),
    (3730, 6),
    (3731, 3),
    (3732, 0),
    (3733, 1),
    (3734, 5),
    (3735, 7),
    (3736, 2),
    (3737, 6),
    (3738, 3),
    (3739, 0),
    (3740, 1),
    (3741, 5),
    (3742, 7),
    (3743, 2),
    (3744, 6),
    (3745, 3),
    (3746, 0),
    (3747, 1),
    (3748, 5),
    (3749, 7),
    (3750, 2),
    (3751, 6),
    (3752, 3),
    (3753, 0),
    (3754, 1),
    (3755, 5),
    (3756, 7),
    (3757, 2),
    (3758, 6),
    (3759, 3),
    (3760, 0),
    (3761, 1),
    (3762, 5),
    (3763, 7),
    (3764, 2),
    (3765, 6),
    (3766, 3),
    (3767, 0),
    (3768, 1),
    (3769, 5),
    (3770, 7),
    (3771, 2),
    (3772, 6),
    (3773, 3),
    (3774, 4),
    (3775, 0),
    (3776, 1),
    (3777, 5),
    (3778, 7),
    (3779, 2),
    (3780, 6),
    (3781, 3),
    (3782, 0),
    (3783, 1),
    (3784, 5),
    (3785, 7),
    (3786, 2),
    (3787, 6),
    (3788, 3),
    (3789, 0),
    (3790, 1),
    (3791, 5),
    (3792, 7),
    (3793, 2),
    (3794, 6),
    (3795, 3),
    (3796, 0),
    (3797, 1),
    (3798, 5),
    (3799, 7),
    (3800, 2),
    (3801, 6),
    (3802, 3),
    (3803, 0),
    (3804, 1),
    (3805, 5),
    (3806, 7),
    (3807, 2),
    (3808, 6),
    (3809, 3),
    (3810, 0),
    (3811, 1),
    (3812, 5),
    (3813, 7),
    (3814, 2),
    (3815, 6),
    (3816, 3),
    (3817, 0),
    (3818, 1),
    (3819, 5),
    (3820, 7),
    (3821, 2),
    (3822, 6),
    (3823, 3),
    (3824, 0),
    (3825, 1),
    (3826, 5),
    (3827, 7),
    (3828, 2),
    (3829, 6),
    (3830, 3),
    (3831, 0),
    (3832, 1),
    (3833, 5),
    (3834, 7),
    (3835, 2),
    (3836, 6),
    (3837, 3),
    (3838, 4)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData29_allowed (j : Fin 128) :
    (3712 + j.val = 0 ∨ (y422TPathRawData29 j).1 < 3712 + j.val) ∧
      (y422TPathRawData29 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
