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
def y422TPathRawData33 : Fin 128 → ℕ × ℕ :=
  ![(4223, 6),
    (4224, 3),
    (4225, 0),
    (2473, 3),
    (109, 3),
    (4228, 2),
    (4229, 3),
    (4054, 4),
    (797, 1),
    (849, 5),
    (4233, 7),
    (4234, 8),
    (4235, 0),
    (4236, 1),
    (4237, 2),
    (4238, 0),
    (4239, 5),
    (319, 7),
    (4241, 8),
    (4242, 0),
    (4243, 1),
    (4244, 2),
    (4245, 5),
    (4246, 6),
    (4247, 0),
    (4248, 7),
    (4249, 8),
    (4250, 0),
    (4251, 1),
    (4252, 2),
    (4253, 0),
    (4254, 5),
    (4255, 6),
    (4256, 0),
    (4257, 7),
    (4258, 8),
    (4259, 0),
    (4260, 1),
    (4261, 2),
    (4262, 0),
    (4263, 5),
    (4264, 6),
    (4265, 0),
    (4266, 7),
    (4267, 8),
    (4268, 0),
    (4269, 1),
    (4270, 2),
    (4271, 0),
    (4272, 5),
    (4273, 6),
    (4274, 0),
    (4275, 7),
    (4276, 8),
    (4277, 0),
    (4278, 1),
    (4279, 2),
    (4280, 0),
    (4281, 5),
    (4282, 6),
    (4283, 0),
    (4284, 7),
    (4285, 8),
    (4286, 0),
    (4287, 1),
    (797, 3),
    (4289, 0),
    (4290, 1),
    (4291, 5),
    (4292, 2),
    (4293, 6),
    (4294, 3),
    (4295, 0),
    (4296, 1),
    (4297, 5),
    (4298, 7),
    (4299, 2),
    (4300, 6),
    (4301, 3),
    (4302, 0),
    (4303, 1),
    (4304, 5),
    (4305, 7),
    (4306, 2),
    (4307, 6),
    (4308, 3),
    (4309, 0),
    (4310, 1),
    (4311, 5),
    (4312, 7),
    (4313, 2),
    (4314, 6),
    (4315, 3),
    (4316, 0),
    (4317, 1),
    (4318, 5),
    (4319, 7),
    (4320, 2),
    (4321, 6),
    (4322, 3),
    (4323, 0),
    (4324, 1),
    (4325, 5),
    (4326, 7),
    (4327, 2),
    (4328, 6),
    (4329, 3),
    (4330, 0),
    (4331, 1),
    (4332, 5),
    (4333, 7),
    (4334, 2),
    (4335, 6),
    (4336, 3),
    (4337, 0),
    (4338, 1),
    (4339, 5),
    (4340, 7),
    (4341, 2),
    (4342, 6),
    (4343, 3),
    (4344, 4),
    (4345, 0),
    (4346, 1),
    (4347, 5),
    (4348, 7),
    (4349, 2),
    (4350, 6)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData33_allowed (j : Fin 128) :
    (4224 + j.val = 0 ∨ (y422TPathRawData33 j).1 < 4224 + j.val) ∧
      (y422TPathRawData33 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
