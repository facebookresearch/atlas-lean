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
def y422TPathRawData43 : Fin 128 → ℕ × ℕ :=
  ![(5503, 0),
    (5504, 7),
    (5505, 8),
    (5506, 0),
    (5507, 1),
    (5508, 2),
    (5509, 0),
    (5510, 5),
    (5511, 6),
    (5512, 0),
    (5513, 7),
    (5514, 8),
    (5515, 0),
    (5516, 1),
    (5517, 2),
    (5518, 0),
    (5519, 5),
    (5520, 6),
    (5521, 0),
    (5522, 7),
    (5523, 8),
    (5524, 0),
    (5525, 1),
    (5526, 2),
    (5527, 0),
    (2517, 3),
    (5529, 0),
    (1337, 2),
    (5531, 6),
    (5532, 3),
    (5533, 1),
    (5534, 5),
    (5535, 7),
    (5536, 2),
    (5537, 3),
    (5538, 0),
    (5539, 1),
    (5540, 5),
    (5541, 7),
    (5542, 2),
    (5543, 6),
    (5544, 3),
    (5545, 0),
    (5546, 1),
    (5547, 5),
    (5548, 7),
    (5549, 2),
    (5550, 6),
    (5551, 3),
    (5552, 0),
    (5553, 1),
    (5554, 5),
    (5555, 7),
    (5556, 2),
    (5557, 6),
    (5558, 3),
    (5559, 0),
    (5560, 1),
    (5561, 5),
    (5562, 7),
    (5563, 2),
    (5564, 6),
    (5565, 3),
    (5566, 0),
    (5567, 1),
    (5568, 5),
    (5569, 7),
    (5570, 2),
    (5571, 6),
    (5572, 3),
    (5573, 0),
    (5574, 1),
    (5575, 5),
    (5576, 7),
    (5577, 2),
    (5578, 6),
    (5579, 3),
    (5580, 4),
    (5581, 0),
    (5582, 1),
    (5583, 5),
    (5584, 7),
    (5585, 2),
    (5586, 6),
    (5587, 3),
    (5588, 0),
    (5589, 1),
    (5590, 5),
    (5591, 7),
    (5592, 2),
    (5593, 6),
    (5594, 3),
    (5595, 0),
    (5596, 1),
    (5597, 5),
    (5598, 7),
    (5599, 2),
    (5600, 6),
    (5601, 3),
    (5602, 0),
    (5603, 1),
    (5604, 5),
    (5605, 7),
    (5606, 2),
    (5607, 6),
    (5608, 3),
    (5609, 0),
    (5610, 1),
    (5611, 5),
    (5612, 7),
    (5613, 2),
    (5614, 6),
    (5615, 3),
    (5616, 0),
    (5617, 1),
    (5618, 5),
    (5619, 7),
    (5620, 2),
    (5621, 6),
    (5622, 3),
    (5623, 0),
    (5624, 1),
    (5625, 5),
    (5626, 7),
    (5627, 2),
    (5628, 6),
    (5629, 3),
    (5630, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData43_allowed (j : Fin 128) :
    (5504 + j.val = 0 ∨ (y422TPathRawData43 j).1 < 5504 + j.val) ∧
      (y422TPathRawData43 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
