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
def y422TPathRawData34 : Fin 128 → ℕ × ℕ :=
  ![(4351, 3),
    (4352, 0),
    (4353, 1),
    (4354, 5),
    (4355, 7),
    (4356, 2),
    (4357, 6),
    (4358, 3),
    (4359, 0),
    (4360, 1),
    (4361, 5),
    (4362, 7),
    (4363, 2),
    (4364, 6),
    (4365, 3),
    (4366, 0),
    (4367, 1),
    (4368, 5),
    (4369, 7),
    (4370, 2),
    (4371, 6),
    (4372, 3),
    (4373, 0),
    (4374, 1),
    (4375, 5),
    (4376, 7),
    (4377, 2),
    (4378, 6),
    (4379, 3),
    (4380, 0),
    (4381, 1),
    (4382, 5),
    (4383, 7),
    (4384, 2),
    (4385, 6),
    (4386, 3),
    (4387, 0),
    (4388, 1),
    (4389, 5),
    (4390, 7),
    (4391, 2),
    (4392, 6),
    (4393, 3),
    (4394, 0),
    (4395, 1),
    (4396, 5),
    (4397, 7),
    (4398, 2),
    (4399, 6),
    (4400, 3),
    (4401, 0),
    (4402, 1),
    (4403, 5),
    (4404, 7),
    (4405, 2),
    (4406, 6),
    (4407, 3),
    (4408, 4),
    (4409, 0),
    (4410, 1),
    (4411, 5),
    (4412, 7),
    (4413, 2),
    (4414, 6),
    (4415, 3),
    (4416, 0),
    (4417, 1),
    (4418, 5),
    (4419, 7),
    (4420, 2),
    (4421, 6),
    (4422, 3),
    (4423, 0),
    (4424, 1),
    (4425, 5),
    (4426, 7),
    (4427, 2),
    (4428, 6),
    (4429, 3),
    (4430, 0),
    (4431, 1),
    (4432, 5),
    (4433, 7),
    (4434, 2),
    (4435, 6),
    (4436, 3),
    (4437, 0),
    (4438, 1),
    (4439, 5),
    (4440, 7),
    (4441, 2),
    (4442, 6),
    (4443, 3),
    (4444, 0),
    (4445, 1),
    (4446, 5),
    (4447, 7),
    (4448, 2),
    (4449, 6),
    (4450, 3),
    (4451, 0),
    (4452, 1),
    (4453, 5),
    (4454, 7),
    (4455, 2),
    (4456, 6),
    (4457, 3),
    (4458, 0),
    (4459, 1),
    (4460, 5),
    (4461, 7),
    (4462, 2),
    (4463, 6),
    (4464, 3),
    (4465, 0),
    (4466, 1),
    (110, 3),
    (111, 0),
    (4469, 5),
    (586, 3),
    (4228, 4),
    (4228, 5),
    (4228, 8),
    (336, 8),
    (2478, 5),
    (314, 7),
    (4477, 8),
    (4478, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData34_allowed (j : Fin 128) :
    (4352 + j.val = 0 ∨ (y422TPathRawData34 j).1 < 4352 + j.val) ∧
      (y422TPathRawData34 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
