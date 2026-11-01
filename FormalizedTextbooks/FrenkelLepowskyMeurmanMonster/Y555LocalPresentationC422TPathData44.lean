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
def y422TPathRawData44 : Fin 128 → ℕ × ℕ :=
  ![(5631, 1),
    (5632, 5),
    (5633, 7),
    (5634, 2),
    (5635, 6),
    (5636, 3),
    (5637, 0),
    (5638, 1),
    (5639, 5),
    (5640, 7),
    (5641, 2),
    (5642, 6),
    (5643, 3),
    (5644, 4),
    (5645, 0),
    (5646, 1),
    (5647, 5),
    (5648, 7),
    (5649, 2),
    (5650, 6),
    (5651, 3),
    (5652, 0),
    (5653, 1),
    (5654, 5),
    (5655, 7),
    (5656, 2),
    (5657, 6),
    (5658, 3),
    (5659, 0),
    (5660, 1),
    (5661, 5),
    (5662, 7),
    (5663, 2),
    (5664, 6),
    (5665, 3),
    (5666, 0),
    (5667, 1),
    (5668, 5),
    (5669, 7),
    (5670, 2),
    (5671, 6),
    (5672, 3),
    (5673, 0),
    (5674, 1),
    (5675, 5),
    (5676, 7),
    (5677, 2),
    (5678, 6),
    (5679, 3),
    (5680, 0),
    (5681, 1),
    (5682, 5),
    (5683, 7),
    (5684, 2),
    (5685, 6),
    (5686, 3),
    (5687, 0),
    (5688, 1),
    (5689, 5),
    (5690, 7),
    (5691, 2),
    (5692, 6),
    (5693, 3),
    (5694, 0),
    (5695, 1),
    (5696, 5),
    (5697, 7),
    (5698, 2),
    (5699, 6),
    (5700, 3),
    (5701, 0),
    (5702, 1),
    (5703, 5),
    (5704, 7),
    (850, 1),
    (850, 3),
    (5446, 3),
    (3464, 3),
    (5709, 2),
    (5710, 3),
    (5454, 4),
    (5454, 5),
    (5454, 6),
    (5454, 8),
    (2477, 6),
    (4937, 8),
    (5706, 2),
    (5718, 0),
    (5719, 5),
    (5720, 6),
    (5721, 0),
    (5722, 7),
    (5723, 8),
    (5724, 1),
    (5725, 2),
    (5726, 0),
    (5727, 5),
    (5728, 6),
    (5729, 0),
    (5730, 7),
    (5731, 8),
    (5732, 0),
    (5733, 1),
    (5734, 2),
    (5735, 0),
    (5736, 5),
    (5737, 6),
    (5738, 0),
    (5739, 7),
    (5740, 8),
    (5741, 0),
    (5742, 1),
    (5743, 2),
    (5744, 0),
    (5745, 5),
    (5746, 6),
    (5747, 0),
    (5748, 7),
    (5749, 8),
    (5750, 0),
    (5751, 1),
    (5752, 2),
    (5753, 0),
    (5754, 5),
    (5755, 6),
    (5756, 0),
    (5757, 7),
    (5758, 8)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData44_allowed (j : Fin 128) :
    (5632 + j.val = 0 ∨ (y422TPathRawData44 j).1 < 5632 + j.val) ∧
      (y422TPathRawData44 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
