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
def y422TPathRawData67 : Fin 128 → ℕ × ℕ :=
  ![(8575, 1),
    (8576, 5),
    (8577, 7),
    (8578, 2),
    (8579, 6),
    (8580, 3),
    (8581, 0),
    (8582, 1),
    (8583, 5),
    (8584, 7),
    (8585, 2),
    (8586, 6),
    (8587, 3),
    (8588, 0),
    (8589, 1),
    (8590, 5),
    (8591, 7),
    (8592, 2),
    (8593, 6),
    (8594, 3),
    (8595, 4),
    (8596, 0),
    (8597, 1),
    (8598, 5),
    (8599, 7),
    (8600, 2),
    (8601, 6),
    (8602, 3),
    (8603, 0),
    (8604, 1),
    (8605, 5),
    (8606, 7),
    (8607, 2),
    (8608, 6),
    (8609, 3),
    (8610, 0),
    (8611, 1),
    (8612, 5),
    (8613, 7),
    (8614, 2),
    (8615, 6),
    (8616, 3),
    (8617, 0),
    (8618, 1),
    (8619, 5),
    (8620, 7),
    (8621, 2),
    (8622, 6),
    (8623, 3),
    (8624, 0),
    (8625, 1),
    (8626, 5),
    (8627, 7),
    (8628, 2),
    (8629, 6),
    (8630, 3),
    (8631, 0),
    (8632, 1),
    (8633, 5),
    (8634, 7),
    (8635, 2),
    (8636, 6),
    (8637, 3),
    (8638, 0),
    (8639, 1),
    (8640, 5),
    (8641, 7),
    (8642, 2),
    (8643, 6),
    (8644, 3),
    (8645, 0),
    (8646, 1),
    (8647, 5),
    (8648, 7),
    (8649, 2),
    (8650, 6),
    (8651, 3),
    (8652, 0),
    (8653, 1),
    (8654, 5),
    (8655, 7),
    (8656, 2),
    (8657, 6),
    (8658, 3),
    (8659, 4),
    (8660, 0),
    (8661, 1),
    (8662, 5),
    (8663, 7),
    (8664, 2),
    (8665, 6),
    (8666, 3),
    (8667, 0),
    (8668, 1),
    (8669, 5),
    (8670, 7),
    (8671, 2),
    (8672, 6),
    (8673, 3),
    (8674, 0),
    (8675, 1),
    (8676, 5),
    (8677, 7),
    (8678, 2),
    (8679, 6),
    (8680, 3),
    (8681, 0),
    (8682, 1),
    (8683, 5),
    (8684, 7),
    (8685, 2),
    (8686, 6),
    (8687, 3),
    (8688, 0),
    (8689, 1),
    (8690, 5),
    (8691, 7),
    (8692, 2),
    (8693, 6),
    (8694, 3),
    (8695, 0),
    (8696, 1),
    (8697, 5),
    (8698, 7),
    (8699, 2),
    (8700, 6),
    (8701, 3),
    (8702, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData67_allowed (j : Fin 128) :
    (8576 + j.val = 0 ∨ (y422TPathRawData67 j).1 < 8576 + j.val) ∧
      (y422TPathRawData67 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
