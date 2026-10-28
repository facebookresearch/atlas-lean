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
def y422TPathRawData35 : Fin 128 → ℕ × ℕ :=
  ![(4479, 1),
    (4480, 2),
    (4481, 0),
    (4482, 5),
    (4483, 6),
    (4484, 0),
    (4485, 7),
    (4486, 8),
    (4487, 0),
    (4488, 1),
    (4489, 2),
    (4490, 0),
    (4491, 5),
    (4492, 6),
    (4493, 0),
    (4494, 7),
    (4495, 8),
    (4496, 0),
    (4497, 1),
    (4498, 2),
    (4499, 0),
    (4500, 5),
    (4501, 6),
    (4502, 0),
    (4503, 7),
    (4504, 8),
    (4505, 0),
    (4506, 1),
    (4507, 2),
    (4508, 0),
    (4509, 5),
    (4510, 6),
    (4511, 0),
    (4512, 7),
    (4513, 8),
    (4514, 0),
    (4515, 1),
    (4516, 2),
    (4517, 0),
    (4518, 5),
    (4519, 6),
    (4520, 0),
    (4521, 7),
    (4232, 3),
    (4523, 0),
    (4524, 1),
    (4525, 5),
    (1335, 2),
    (4527, 3),
    (4528, 0),
    (4529, 1),
    (4530, 7),
    (4531, 2),
    (4532, 3),
    (4533, 0),
    (4534, 1),
    (4535, 5),
    (4536, 7),
    (4537, 2),
    (4538, 6),
    (4539, 3),
    (4540, 0),
    (4541, 1),
    (4542, 5),
    (4543, 7),
    (4544, 2),
    (4545, 6),
    (4546, 3),
    (4547, 0),
    (4548, 1),
    (4549, 5),
    (4550, 7),
    (4551, 2),
    (4552, 6),
    (4553, 3),
    (4554, 0),
    (4555, 1),
    (4556, 5),
    (4557, 7),
    (4558, 2),
    (4559, 6),
    (4560, 3),
    (4561, 0),
    (4562, 1),
    (4563, 5),
    (4564, 7),
    (4565, 2),
    (4566, 6),
    (4567, 3),
    (4568, 0),
    (4569, 1),
    (4570, 5),
    (4571, 7),
    (4572, 2),
    (4573, 6),
    (4574, 3),
    (4575, 4),
    (4576, 0),
    (4577, 1),
    (4578, 5),
    (4579, 7),
    (4580, 2),
    (4581, 6),
    (4582, 3),
    (4583, 0),
    (4584, 1),
    (4585, 5),
    (4586, 7),
    (4587, 2),
    (4588, 6),
    (4589, 3),
    (4590, 0),
    (4591, 1),
    (4592, 5),
    (4593, 7),
    (4594, 2),
    (4595, 6),
    (4596, 3),
    (4597, 0),
    (4598, 1),
    (4599, 5),
    (4600, 7),
    (4601, 2),
    (4602, 6),
    (4603, 3),
    (4604, 0),
    (4605, 1),
    (4606, 5)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData35_allowed (j : Fin 128) :
    (4480 + j.val = 0 ∨ (y422TPathRawData35 j).1 < 4480 + j.val) ∧
      (y422TPathRawData35 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
