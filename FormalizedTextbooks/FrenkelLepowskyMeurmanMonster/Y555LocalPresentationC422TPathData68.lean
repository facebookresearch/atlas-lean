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
def y422TPathRawData68 : Fin 128 → ℕ × ℕ :=
  ![(8703, 1),
    (8704, 5),
    (8705, 7),
    (8706, 2),
    (8707, 6),
    (8708, 3),
    (8709, 0),
    (8710, 1),
    (8711, 5),
    (8712, 7),
    (8713, 2),
    (8714, 6),
    (8715, 3),
    (8716, 0),
    (8717, 1),
    (8718, 5),
    (8719, 7),
    (8248, 3),
    (8248, 5),
    (8722, 0),
    (8723, 5),
    (127, 3),
    (8725, 2),
    (8726, 3),
    (127, 6),
    (8450, 4),
    (8450, 5),
    (8450, 6),
    (8450, 8),
    (7968, 7),
    (7443, 7),
    (8734, 8),
    (8735, 0),
    (8736, 1),
    (8737, 2),
    (8738, 0),
    (8739, 5),
    (8740, 6),
    (8741, 0),
    (8742, 7),
    (8743, 8),
    (8744, 0),
    (8745, 1),
    (8746, 2),
    (8747, 0),
    (8748, 5),
    (8749, 6),
    (8750, 0),
    (8751, 7),
    (8752, 8),
    (8753, 0),
    (8754, 1),
    (8755, 2),
    (8756, 0),
    (8757, 5),
    (8758, 6),
    (8759, 0),
    (8760, 7),
    (8761, 8),
    (8762, 0),
    (8763, 1),
    (8764, 2),
    (8765, 0),
    (8766, 5),
    (8767, 6),
    (8768, 0),
    (8769, 7),
    (8770, 8),
    (8771, 0),
    (8772, 1),
    (8773, 2),
    (8774, 0),
    (8775, 5),
    (8776, 6),
    (8777, 0),
    (8778, 7),
    (8779, 8),
    (8780, 0),
    (8781, 1),
    (8782, 2),
    (8783, 0),
    (8784, 5),
    (8785, 6),
    (8786, 0),
    (8787, 7),
    (8788, 8),
    (8789, 0),
    (8790, 1),
    (8791, 2),
    (8792, 0),
    (8793, 5),
    (8794, 6),
    (8795, 0),
    (8796, 7),
    (8797, 8),
    (8798, 0),
    (8799, 1),
    (8800, 2),
    (8801, 0),
    (8802, 5),
    (8803, 6),
    (8804, 0),
    (8805, 7),
    (8806, 8),
    (8807, 0),
    (8808, 1),
    (8249, 5),
    (8810, 7),
    (8811, 2),
    (8463, 3),
    (8813, 0),
    (8814, 1),
    (8815, 5),
    (8816, 2),
    (8817, 6),
    (8818, 3),
    (8819, 0),
    (8820, 1),
    (8821, 5),
    (8822, 7),
    (8823, 2),
    (8824, 6),
    (8825, 3),
    (8826, 0),
    (8827, 1),
    (8828, 5),
    (8829, 7),
    (8830, 2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData68_allowed (j : Fin 128) :
    (8704 + j.val = 0 ∨ (y422TPathRawData68 j).1 < 8704 + j.val) ∧
      (y422TPathRawData68 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
