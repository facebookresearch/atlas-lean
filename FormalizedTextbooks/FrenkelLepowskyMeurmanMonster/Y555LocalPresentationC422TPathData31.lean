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
def y422TPathRawData31 : Fin 128 → ℕ × ℕ :=
  ![(3967, 6),
    (3968, 3),
    (3969, 0),
    (3970, 1),
    (3971, 5),
    (3972, 7),
    (3973, 2),
    (3974, 6),
    (3975, 3),
    (3976, 0),
    (3977, 1),
    (3978, 5),
    (3979, 7),
    (3980, 2),
    (3981, 6),
    (3982, 3),
    (3983, 0),
    (3984, 1),
    (3985, 5),
    (3986, 7),
    (3987, 2),
    (3988, 6),
    (3989, 3),
    (3990, 0),
    (3991, 1),
    (3992, 5),
    (3993, 7),
    (3994, 2),
    (3995, 6),
    (3996, 3),
    (3997, 0),
    (3998, 1),
    (3999, 5),
    (4000, 7),
    (4001, 2),
    (4002, 6),
    (4003, 3),
    (4004, 4),
    (4005, 0),
    (4006, 1),
    (4007, 5),
    (4008, 7),
    (4009, 2),
    (4010, 6),
    (4011, 3),
    (4012, 0),
    (4013, 1),
    (4014, 5),
    (4015, 7),
    (4016, 2),
    (4017, 6),
    (4018, 3),
    (4019, 0),
    (4020, 1),
    (4021, 5),
    (4022, 7),
    (4023, 2),
    (4024, 6),
    (4025, 3),
    (4026, 0),
    (4027, 1),
    (4028, 5),
    (4029, 7),
    (4030, 2),
    (4031, 6),
    (4032, 3),
    (4033, 0),
    (4034, 1),
    (4035, 5),
    (4036, 7),
    (4037, 2),
    (4038, 6),
    (4039, 3),
    (4040, 0),
    (4041, 1),
    (4042, 5),
    (4043, 7),
    (4044, 2),
    (4045, 6),
    (4046, 3),
    (4047, 0),
    (4048, 1),
    (4049, 5),
    (4050, 7),
    (4051, 2),
    (4052, 6),
    (108, 3),
    (3882, 4),
    (3882, 5),
    (1134, 7),
    (1277, 6),
    (2225, 1),
    (4048, 2),
    (4060, 6),
    (4061, 3),
    (4062, 0),
    (4063, 1),
    (4064, 5),
    (4065, 7),
    (4066, 2),
    (4067, 6),
    (4068, 3),
    (4069, 0),
    (4070, 1),
    (4071, 5),
    (4072, 7),
    (4073, 2),
    (4074, 6),
    (4075, 3),
    (4076, 0),
    (4077, 1),
    (4078, 5),
    (4079, 7),
    (4080, 2),
    (4081, 6),
    (4082, 3),
    (4083, 0),
    (4084, 1),
    (4085, 5),
    (4086, 7),
    (4087, 2),
    (4088, 6),
    (4089, 3),
    (4090, 0),
    (4091, 1),
    (4092, 5),
    (4093, 7),
    (4094, 2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData31_allowed (j : Fin 128) :
    (3968 + j.val = 0 ∨ (y422TPathRawData31 j).1 < 3968 + j.val) ∧
      (y422TPathRawData31 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
