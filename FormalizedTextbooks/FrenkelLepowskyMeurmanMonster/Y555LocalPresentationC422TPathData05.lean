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
def y422TPathRawData05 : Fin 128 → ℕ × ℕ :=
  ![(639, 0),
    (640, 5),
    (641, 6),
    (642, 0),
    (643, 7),
    (644, 8),
    (645, 0),
    (646, 1),
    (647, 2),
    (648, 0),
    (280, 1),
    (650, 2),
    (651, 6),
    (652, 5),
    (399, 3),
    (264, 3),
    (279, 2),
    (177, 0),
    (657, 6),
    (81, 8),
    (659, 1),
    (635, 5),
    (661, 6),
    (662, 7),
    (663, 8),
    (664, 0),
    (665, 1),
    (666, 2),
    (667, 5),
    (668, 6),
    (669, 0),
    (670, 7),
    (671, 8),
    (672, 0),
    (673, 1),
    (674, 2),
    (675, 0),
    (676, 5),
    (677, 6),
    (678, 0),
    (679, 7),
    (680, 8),
    (681, 0),
    (682, 1),
    (683, 2),
    (684, 0),
    (685, 5),
    (686, 6),
    (687, 0),
    (688, 7),
    (689, 8),
    (690, 0),
    (691, 1),
    (692, 2),
    (693, 0),
    (694, 5),
    (695, 6),
    (696, 0),
    (697, 7),
    (698, 8),
    (699, 0),
    (700, 1),
    (701, 2),
    (702, 0),
    (703, 5),
    (704, 6),
    (705, 0),
    (706, 7),
    (707, 8),
    (708, 0),
    (709, 1),
    (710, 2),
    (711, 0),
    (379, 0),
    (713, 5),
    (714, 6),
    (178, 5),
    (102, 7),
    (717, 0),
    (718, 1),
    (719, 2),
    (720, 5),
    (721, 6),
    (722, 0),
    (723, 7),
    (724, 8),
    (725, 0),
    (726, 1),
    (727, 2),
    (728, 0),
    (729, 5),
    (730, 6),
    (731, 0),
    (732, 7),
    (733, 8),
    (734, 0),
    (735, 1),
    (736, 2),
    (737, 0),
    (738, 5),
    (739, 6),
    (740, 0),
    (741, 7),
    (742, 8),
    (743, 0),
    (744, 1),
    (745, 2),
    (746, 0),
    (747, 5),
    (748, 6),
    (749, 0),
    (750, 7),
    (751, 8),
    (752, 0),
    (753, 1),
    (754, 2),
    (755, 0),
    (756, 5),
    (757, 6),
    (758, 0),
    (759, 7),
    (760, 8),
    (761, 0),
    (762, 1),
    (763, 2),
    (764, 0),
    (765, 5),
    (766, 6)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData05_allowed (j : Fin 128) :
    (640 + j.val = 0 ∨ (y422TPathRawData05 j).1 < 640 + j.val) ∧
      (y422TPathRawData05 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
