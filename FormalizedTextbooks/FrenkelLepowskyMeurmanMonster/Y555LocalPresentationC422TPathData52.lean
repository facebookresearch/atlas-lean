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
def y422TPathRawData52 : Fin 128 → ℕ × ℕ :=
  ![(6655, 1),
    (6656, 2),
    (6657, 0),
    (6658, 5),
    (6659, 6),
    (6660, 0),
    (6661, 7),
    (6662, 8),
    (6663, 0),
    (6664, 1),
    (6665, 2),
    (6666, 0),
    (6667, 5),
    (6668, 6),
    (6669, 0),
    (6670, 7),
    (6671, 8),
    (6672, 0),
    (6673, 1),
    (6674, 2),
    (6675, 0),
    (6676, 5),
    (6677, 6),
    (6678, 0),
    (6679, 7),
    (6680, 8),
    (6681, 0),
    (6682, 1),
    (6683, 2),
    (6684, 0),
    (6685, 5),
    (6686, 6),
    (6687, 0),
    (6688, 7),
    (6689, 8),
    (6690, 0),
    (6691, 1),
    (6692, 2),
    (6693, 0),
    (6694, 5),
    (6695, 6),
    (6696, 0),
    (6697, 7),
    (6698, 8),
    (6699, 0),
    (6700, 1),
    (6701, 2),
    (6702, 0),
    (6703, 5),
    (6704, 6),
    (6705, 0),
    (6706, 7),
    (120, 7),
    (882, 6),
    (6709, 3),
    (6710, 0),
    (6711, 1),
    (6712, 5),
    (6713, 7),
    (6714, 2),
    (6715, 6),
    (6716, 3),
    (6717, 0),
    (6718, 1),
    (6719, 5),
    (6720, 7),
    (6721, 2),
    (6722, 6),
    (6723, 3),
    (6724, 0),
    (6725, 1),
    (6726, 5),
    (6727, 7),
    (6728, 2),
    (6729, 6),
    (6730, 3),
    (6731, 0),
    (6732, 1),
    (6733, 5),
    (6734, 7),
    (6735, 2),
    (6736, 6),
    (6737, 3),
    (6738, 0),
    (6739, 1),
    (6740, 5),
    (6741, 7),
    (6742, 2),
    (6743, 6),
    (6744, 3),
    (6745, 0),
    (6746, 1),
    (6747, 5),
    (6748, 7),
    (6749, 2),
    (6750, 6),
    (6751, 3),
    (6752, 0),
    (6753, 1),
    (6754, 5),
    (6755, 7),
    (6756, 2),
    (6757, 6),
    (6758, 3),
    (6759, 0),
    (6760, 1),
    (6761, 5),
    (6762, 7),
    (6763, 2),
    (6764, 6),
    (6765, 3),
    (6766, 4),
    (6767, 0),
    (6768, 1),
    (6769, 5),
    (6770, 7),
    (6771, 2),
    (6772, 6),
    (6773, 3),
    (6774, 0),
    (6775, 1),
    (6776, 5),
    (6777, 7),
    (6778, 2),
    (6779, 6),
    (6780, 3),
    (6781, 0),
    (6782, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData52_allowed (j : Fin 128) :
    (6656 + j.val = 0 ∨ (y422TPathRawData52 j).1 < 6656 + j.val) ∧
      (y422TPathRawData52 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
