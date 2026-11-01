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
def y422TPathRawData32 : Fin 128 → ℕ × ℕ :=
  ![(4095, 6),
    (4096, 3),
    (4097, 0),
    (4098, 1),
    (4099, 5),
    (4100, 7),
    (4101, 2),
    (4102, 6),
    (4103, 3),
    (4104, 4),
    (4105, 0),
    (4106, 1),
    (4107, 5),
    (4108, 7),
    (4109, 2),
    (4110, 6),
    (4111, 3),
    (4112, 0),
    (4113, 1),
    (4114, 5),
    (4115, 7),
    (4116, 2),
    (4117, 6),
    (4118, 3),
    (4119, 0),
    (4120, 1),
    (4121, 5),
    (4122, 7),
    (4123, 2),
    (4124, 6),
    (4125, 3),
    (4126, 0),
    (4127, 1),
    (4128, 5),
    (4129, 7),
    (4130, 2),
    (4131, 6),
    (4132, 3),
    (4133, 0),
    (4134, 1),
    (4135, 5),
    (4136, 7),
    (4137, 2),
    (4138, 6),
    (4139, 3),
    (4140, 0),
    (4141, 1),
    (4142, 5),
    (4143, 7),
    (4144, 2),
    (4145, 6),
    (4146, 3),
    (4147, 0),
    (4148, 1),
    (4149, 5),
    (4150, 7),
    (4151, 2),
    (4152, 6),
    (4153, 3),
    (4154, 0),
    (4155, 1),
    (4156, 5),
    (4157, 7),
    (4158, 2),
    (4159, 6),
    (4160, 3),
    (4161, 0),
    (4162, 1),
    (4163, 5),
    (4164, 7),
    (4165, 2),
    (4166, 6),
    (4167, 3),
    (4168, 4),
    (4169, 0),
    (4170, 1),
    (4171, 5),
    (4172, 7),
    (4173, 2),
    (4174, 6),
    (4175, 3),
    (4176, 0),
    (4177, 1),
    (4178, 5),
    (4179, 7),
    (4180, 2),
    (4181, 6),
    (4182, 3),
    (4183, 0),
    (4184, 1),
    (4185, 5),
    (4186, 7),
    (4187, 2),
    (4188, 6),
    (4189, 3),
    (4190, 0),
    (4191, 1),
    (4192, 5),
    (4193, 7),
    (4194, 2),
    (4195, 6),
    (4196, 3),
    (4197, 0),
    (4198, 1),
    (4199, 5),
    (4200, 7),
    (4201, 2),
    (4202, 6),
    (4203, 3),
    (4204, 0),
    (4205, 1),
    (4206, 5),
    (4207, 7),
    (4208, 2),
    (4209, 6),
    (4210, 3),
    (4211, 0),
    (4212, 1),
    (4213, 5),
    (4214, 7),
    (4215, 2),
    (4216, 6),
    (4217, 3),
    (4218, 0),
    (4219, 1),
    (4220, 5),
    (4221, 7),
    (4222, 2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData32_allowed (j : Fin 128) :
    (4096 + j.val = 0 ∨ (y422TPathRawData32 j).1 < 4096 + j.val) ∧
      (y422TPathRawData32 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
