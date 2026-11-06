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
def y422TPathRawData04 : Fin 128 → ℕ × ℕ :=
  ![(511, 6),
    (512, 3),
    (513, 0),
    (514, 1),
    (515, 5),
    (516, 7),
    (517, 2),
    (518, 6),
    (519, 3),
    (520, 0),
    (521, 1),
    (522, 5),
    (523, 7),
    (524, 2),
    (525, 6),
    (526, 3),
    (527, 0),
    (528, 1),
    (529, 5),
    (530, 7),
    (531, 2),
    (532, 6),
    (533, 3),
    (534, 0),
    (535, 1),
    (536, 5),
    (537, 7),
    (538, 2),
    (539, 6),
    (540, 3),
    (541, 4),
    (542, 0),
    (543, 1),
    (544, 5),
    (545, 7),
    (546, 2),
    (547, 6),
    (548, 3),
    (549, 0),
    (550, 1),
    (551, 5),
    (552, 7),
    (553, 2),
    (554, 6),
    (555, 3),
    (556, 0),
    (557, 1),
    (558, 5),
    (559, 7),
    (560, 2),
    (561, 6),
    (562, 3),
    (563, 0),
    (564, 1),
    (565, 5),
    (566, 7),
    (567, 2),
    (568, 6),
    (569, 3),
    (570, 0),
    (571, 1),
    (572, 5),
    (573, 7),
    (574, 2),
    (575, 6),
    (576, 3),
    (577, 0),
    (578, 1),
    (579, 5),
    (92, 8),
    (100, 5),
    (347, 8),
    (583, 0),
    (584, 1),
    (585, 2),
    (586, 5),
    (587, 6),
    (588, 0),
    (589, 7),
    (590, 8),
    (591, 0),
    (592, 1),
    (593, 2),
    (594, 0),
    (595, 5),
    (596, 6),
    (597, 0),
    (598, 7),
    (599, 8),
    (600, 0),
    (601, 1),
    (602, 2),
    (603, 0),
    (604, 5),
    (605, 6),
    (606, 0),
    (607, 7),
    (608, 8),
    (609, 0),
    (610, 1),
    (611, 2),
    (612, 0),
    (613, 5),
    (614, 6),
    (615, 0),
    (616, 7),
    (617, 8),
    (618, 0),
    (619, 1),
    (620, 2),
    (621, 0),
    (622, 5),
    (623, 6),
    (624, 0),
    (625, 7),
    (626, 8),
    (627, 0),
    (628, 1),
    (629, 2),
    (630, 0),
    (631, 5),
    (632, 6),
    (633, 0),
    (634, 7),
    (635, 8),
    (636, 0),
    (637, 1),
    (638, 2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData04_allowed (j : Fin 128) :
    (512 + j.val = 0 ∨ (y422TPathRawData04 j).1 < 512 + j.val) ∧
      (y422TPathRawData04 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
