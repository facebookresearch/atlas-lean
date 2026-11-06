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
def y422TPathRawData53 : Fin 128 → ℕ × ℕ :=
  ![(6783, 5),
    (6784, 7),
    (6785, 2),
    (6786, 6),
    (6787, 3),
    (6788, 0),
    (6789, 1),
    (6790, 5),
    (6791, 7),
    (6792, 2),
    (6793, 6),
    (6794, 3),
    (6795, 0),
    (6796, 1),
    (6797, 5),
    (6798, 7),
    (6799, 2),
    (6800, 6),
    (6801, 3),
    (6802, 0),
    (6803, 1),
    (6804, 5),
    (6805, 7),
    (6806, 2),
    (6807, 6),
    (6808, 3),
    (6809, 0),
    (6810, 1),
    (6811, 5),
    (6812, 7),
    (6813, 2),
    (6814, 6),
    (6815, 3),
    (6816, 0),
    (6817, 1),
    (6818, 5),
    (6819, 7),
    (6820, 2),
    (6821, 6),
    (6822, 3),
    (6823, 0),
    (6824, 1),
    (6825, 5),
    (6826, 7),
    (6827, 2),
    (6828, 6),
    (6829, 3),
    (6830, 4),
    (6831, 0),
    (6832, 1),
    (6833, 5),
    (6834, 7),
    (6835, 2),
    (6836, 6),
    (6837, 3),
    (6838, 0),
    (6839, 1),
    (6840, 5),
    (6841, 7),
    (6842, 2),
    (6843, 6),
    (6844, 3),
    (6845, 0),
    (6846, 1),
    (6847, 5),
    (6848, 7),
    (6849, 2),
    (6850, 6),
    (6851, 3),
    (6852, 0),
    (6853, 1),
    (6854, 5),
    (6855, 7),
    (6856, 2),
    (6857, 6),
    (6858, 3),
    (6859, 0),
    (6860, 1),
    (6861, 5),
    (6862, 7),
    (6863, 2),
    (6864, 6),
    (6865, 3),
    (6866, 0),
    (6867, 1),
    (6868, 5),
    (6869, 7),
    (6870, 2),
    (6871, 6),
    (6872, 3),
    (6873, 0),
    (6874, 1),
    (6875, 5),
    (6876, 7),
    (6877, 2),
    (6878, 6),
    (6879, 3),
    (6880, 0),
    (6881, 1),
    (6882, 5),
    (6883, 7),
    (6884, 2),
    (6885, 6),
    (6886, 3),
    (6887, 0),
    (6888, 1),
    (6889, 5),
    (6890, 7),
    (6371, 2),
    (6892, 3),
    (6642, 4),
    (6642, 5),
    (6642, 6),
    (6642, 7),
    (6642, 8),
    (121, 5),
    (6899, 6),
    (6645, 7),
    (6645, 8),
    (3467, 5),
    (6903, 0),
    (6904, 7),
    (6905, 8),
    (6906, 1),
    (6907, 2),
    (6908, 0),
    (6909, 5),
    (6910, 6)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData53_allowed (j : Fin 128) :
    (6784 + j.val = 0 ∨ (y422TPathRawData53 j).1 < 6784 + j.val) ∧
      (y422TPathRawData53 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
