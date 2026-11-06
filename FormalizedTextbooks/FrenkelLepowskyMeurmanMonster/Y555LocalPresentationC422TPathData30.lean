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
def y422TPathRawData30 : Fin 128 → ℕ × ℕ :=
  ![(3839, 0),
    (3840, 1),
    (3841, 5),
    (3842, 7),
    (3843, 2),
    (3844, 6),
    (3845, 3),
    (3846, 0),
    (3847, 1),
    (3848, 5),
    (3849, 7),
    (3850, 2),
    (3851, 6),
    (3852, 3),
    (3853, 0),
    (3854, 1),
    (3855, 5),
    (3856, 7),
    (3857, 2),
    (3858, 6),
    (3859, 3),
    (3860, 0),
    (3861, 1),
    (3862, 5),
    (3863, 7),
    (3864, 2),
    (3865, 6),
    (3866, 3),
    (3867, 0),
    (3868, 1),
    (3869, 5),
    (3870, 7),
    (3871, 2),
    (3872, 6),
    (3873, 3),
    (3874, 0),
    (3875, 1),
    (3876, 5),
    (3877, 7),
    (3878, 2),
    (3879, 6),
    (3880, 3),
    (107, 3),
    (985, 4),
    (307, 3),
    (3884, 0),
    (3885, 1),
    (3886, 5),
    (3887, 7),
    (3888, 2),
    (3889, 6),
    (3890, 3),
    (3891, 0),
    (3892, 1),
    (3893, 5),
    (3894, 7),
    (3895, 2),
    (3896, 6),
    (3897, 3),
    (3898, 0),
    (3899, 1),
    (3900, 5),
    (3901, 7),
    (3902, 2),
    (3903, 6),
    (3904, 3),
    (3905, 0),
    (3906, 1),
    (3907, 5),
    (3908, 7),
    (3909, 2),
    (3910, 6),
    (3911, 3),
    (3912, 0),
    (3913, 1),
    (3914, 5),
    (3915, 7),
    (3916, 2),
    (3917, 6),
    (3918, 3),
    (3919, 0),
    (3920, 1),
    (3921, 5),
    (3922, 7),
    (3923, 2),
    (3924, 6),
    (3925, 3),
    (3926, 0),
    (3927, 1),
    (3928, 5),
    (3929, 7),
    (3930, 2),
    (3931, 6),
    (3932, 3),
    (3933, 0),
    (3934, 1),
    (3935, 5),
    (3936, 7),
    (3937, 2),
    (3938, 6),
    (3939, 3),
    (3940, 4),
    (3941, 0),
    (3942, 1),
    (3943, 5),
    (3944, 7),
    (3945, 2),
    (3946, 6),
    (3947, 3),
    (3948, 0),
    (3949, 1),
    (3950, 5),
    (3951, 7),
    (3952, 2),
    (3953, 6),
    (3954, 3),
    (3955, 0),
    (3956, 1),
    (3957, 5),
    (3958, 7),
    (3959, 2),
    (3960, 6),
    (3961, 3),
    (3962, 0),
    (3963, 1),
    (3964, 5),
    (3965, 7),
    (3966, 2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData30_allowed (j : Fin 128) :
    (3840 + j.val = 0 ∨ (y422TPathRawData30 j).1 < 3840 + j.val) ∧
      (y422TPathRawData30 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
