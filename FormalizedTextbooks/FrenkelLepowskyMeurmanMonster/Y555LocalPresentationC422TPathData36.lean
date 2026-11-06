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
def y422TPathRawData36 : Fin 128 → ℕ × ℕ :=
  ![(4607, 7),
    (4608, 2),
    (4609, 6),
    (4610, 3),
    (4611, 0),
    (4612, 1),
    (4613, 5),
    (4614, 7),
    (4615, 2),
    (4616, 6),
    (4617, 3),
    (4618, 0),
    (4619, 1),
    (4620, 5),
    (4621, 7),
    (4622, 2),
    (4623, 6),
    (4624, 3),
    (4625, 0),
    (4626, 1),
    (4627, 5),
    (4628, 7),
    (4629, 2),
    (4630, 6),
    (4631, 3),
    (4632, 0),
    (4633, 1),
    (4634, 5),
    (4635, 7),
    (4636, 2),
    (4637, 6),
    (4638, 3),
    (4639, 4),
    (4640, 0),
    (4641, 1),
    (4642, 5),
    (4643, 7),
    (4644, 2),
    (4645, 6),
    (4646, 3),
    (4647, 0),
    (4648, 1),
    (4649, 5),
    (4650, 7),
    (4651, 2),
    (4652, 6),
    (4653, 3),
    (4654, 0),
    (4655, 1),
    (4656, 5),
    (4657, 7),
    (4658, 2),
    (4659, 6),
    (4660, 3),
    (4661, 0),
    (4662, 1),
    (4663, 5),
    (4664, 7),
    (4665, 2),
    (4666, 6),
    (4667, 3),
    (4668, 0),
    (4669, 1),
    (4670, 5),
    (4671, 7),
    (4672, 2),
    (4673, 6),
    (4674, 3),
    (4675, 0),
    (4676, 1),
    (4677, 5),
    (4678, 7),
    (4679, 2),
    (4680, 6),
    (4681, 3),
    (4682, 0),
    (4683, 1),
    (4684, 5),
    (4685, 7),
    (4686, 2),
    (4687, 6),
    (4688, 3),
    (4689, 0),
    (4690, 1),
    (4691, 5),
    (4692, 7),
    (4693, 2),
    (4694, 6),
    (4695, 3),
    (4696, 0),
    (4697, 1),
    (4227, 2),
    (4699, 3),
    (4468, 4),
    (4468, 5),
    (4468, 7),
    (4468, 8),
    (2414, 6),
    (4705, 0),
    (590, 5),
    (2463, 7),
    (4708, 8),
    (4709, 0),
    (4710, 1),
    (4711, 2),
    (4712, 0),
    (4713, 5),
    (4714, 6),
    (4715, 0),
    (4716, 7),
    (4717, 8),
    (4718, 0),
    (4719, 1),
    (4720, 2),
    (4721, 0),
    (4722, 5),
    (4723, 6),
    (4724, 0),
    (4725, 7),
    (4726, 8),
    (4727, 0),
    (4728, 1),
    (4729, 2),
    (4730, 0),
    (4731, 5),
    (4732, 6),
    (4733, 0),
    (4734, 7)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData36_allowed (j : Fin 128) :
    (4608 + j.val = 0 ∨ (y422TPathRawData36 j).1 < 4608 + j.val) ∧
      (y422TPathRawData36 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
