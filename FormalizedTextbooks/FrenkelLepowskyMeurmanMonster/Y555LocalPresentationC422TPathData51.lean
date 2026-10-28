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
def y422TPathRawData51 : Fin 128 → ℕ × ℕ :=
  ![(6527, 7),
    (6528, 2),
    (6529, 6),
    (6530, 3),
    (6531, 0),
    (6532, 1),
    (6533, 5),
    (6534, 7),
    (6535, 2),
    (6536, 6),
    (6537, 3),
    (6538, 0),
    (6539, 1),
    (6540, 5),
    (6541, 7),
    (6542, 2),
    (6543, 6),
    (6544, 3),
    (6545, 0),
    (6546, 1),
    (6547, 5),
    (6548, 7),
    (6549, 2),
    (6550, 6),
    (6551, 3),
    (6552, 0),
    (6553, 1),
    (6554, 5),
    (6555, 7),
    (6556, 2),
    (6557, 6),
    (6558, 3),
    (6559, 0),
    (6560, 1),
    (6561, 5),
    (6562, 7),
    (6563, 2),
    (6564, 6),
    (6565, 3),
    (6566, 0),
    (6567, 1),
    (6568, 5),
    (6569, 7),
    (6570, 2),
    (6571, 6),
    (6572, 3),
    (6573, 0),
    (6574, 1),
    (6575, 5),
    (6576, 7),
    (6577, 2),
    (6578, 6),
    (6579, 3),
    (6580, 4),
    (6581, 0),
    (6582, 1),
    (6583, 5),
    (6584, 7),
    (6585, 2),
    (6586, 6),
    (6587, 3),
    (6588, 0),
    (6589, 1),
    (6590, 5),
    (6591, 7),
    (6592, 2),
    (6593, 6),
    (6594, 3),
    (6595, 0),
    (6596, 1),
    (6597, 5),
    (6598, 7),
    (6599, 2),
    (6600, 6),
    (6601, 3),
    (6602, 0),
    (6603, 1),
    (6604, 5),
    (6605, 7),
    (6606, 2),
    (6607, 6),
    (6608, 3),
    (6609, 0),
    (6610, 1),
    (6611, 5),
    (6612, 7),
    (6613, 2),
    (6614, 6),
    (6615, 3),
    (6616, 0),
    (6617, 1),
    (6618, 5),
    (6619, 7),
    (6620, 2),
    (6621, 6),
    (6622, 3),
    (6623, 0),
    (6624, 1),
    (6625, 5),
    (6626, 7),
    (6627, 2),
    (6628, 6),
    (6629, 3),
    (6630, 0),
    (6631, 1),
    (6632, 5),
    (6633, 7),
    (6634, 2),
    (6635, 6),
    (6636, 3),
    (6637, 0),
    (6638, 1),
    (6639, 5),
    (6640, 7),
    (119, 3),
    (120, 0),
    (6643, 5),
    (119, 6),
    (119, 7),
    (2360, 3),
    (2360, 6),
    (6373, 4),
    (6373, 6),
    (6373, 8),
    (5997, 8),
    (6376, 8),
    (5718, 7),
    (4264, 8)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData51_allowed (j : Fin 128) :
    (6528 + j.val = 0 ∨ (y422TPathRawData51 j).1 < 6528 + j.val) ∧
      (y422TPathRawData51 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
