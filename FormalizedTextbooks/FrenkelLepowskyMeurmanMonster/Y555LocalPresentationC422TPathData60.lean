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
def y422TPathRawData60 : Fin 128 → ℕ × ℕ :=
  ![(7679, 5),
    (7680, 7),
    (7681, 2),
    (7682, 6),
    (7683, 3),
    (7684, 0),
    (7685, 1),
    (7686, 5),
    (7687, 7),
    (7688, 2),
    (7689, 6),
    (7690, 3),
    (7691, 0),
    (7692, 1),
    (7693, 5),
    (7694, 7),
    (7695, 2),
    (7696, 6),
    (7697, 3),
    (7698, 0),
    (7699, 1),
    (7700, 5),
    (320, 2),
    (7427, 3),
    (7427, 8),
    (2366, 3),
    (7705, 2),
    (7706, 3),
    (2366, 8),
    (7428, 4),
    (7428, 7),
    (7428, 8),
    (881, 1),
    (7712, 2),
    (7713, 0),
    (7714, 5),
    (7715, 6),
    (7716, 7),
    (7717, 8),
    (7718, 0),
    (7719, 1),
    (7720, 2),
    (7721, 0),
    (7722, 5),
    (7723, 6),
    (7724, 0),
    (7725, 7),
    (7726, 8),
    (7727, 0),
    (7728, 1),
    (7729, 2),
    (7730, 0),
    (7731, 5),
    (7732, 6),
    (7733, 0),
    (7734, 7),
    (7735, 8),
    (7736, 0),
    (7737, 1),
    (7738, 2),
    (7739, 0),
    (7740, 5),
    (7741, 6),
    (7742, 0),
    (7743, 7),
    (7744, 8),
    (7745, 0),
    (7746, 1),
    (7747, 2),
    (7748, 0),
    (7749, 5),
    (7750, 6),
    (7751, 0),
    (7752, 7),
    (7753, 8),
    (7754, 0),
    (7755, 1),
    (7756, 2),
    (7757, 0),
    (7758, 5),
    (7759, 6),
    (7760, 0),
    (7761, 7),
    (7762, 8),
    (7763, 0),
    (7764, 1),
    (7765, 2),
    (7766, 0),
    (7767, 5),
    (7768, 6),
    (7769, 0),
    (7770, 7),
    (7771, 8),
    (7772, 0),
    (7773, 1),
    (7774, 2),
    (7775, 0),
    (7776, 5),
    (7777, 6),
    (7778, 0),
    (7779, 7),
    (7780, 8),
    (7781, 0),
    (7782, 1),
    (7783, 2),
    (7784, 0),
    (7785, 5),
    (7438, 2),
    (2393, 3),
    (7788, 0),
    (7789, 1),
    (7790, 2),
    (7791, 6),
    (7792, 3),
    (7793, 0),
    (7794, 1),
    (7795, 5),
    (7796, 7),
    (7797, 2),
    (7798, 6),
    (7799, 3),
    (7800, 0),
    (7801, 1),
    (7802, 5),
    (7803, 7),
    (7804, 2),
    (7805, 6),
    (7806, 3)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData60_allowed (j : Fin 128) :
    (7680 + j.val = 0 ∨ (y422TPathRawData60 j).1 < 7680 + j.val) ∧
      (y422TPathRawData60 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
