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
def y422TPathRawData61 : Fin 128 → ℕ × ℕ :=
  ![(7807, 0),
    (7808, 1),
    (7809, 5),
    (7810, 7),
    (7811, 2),
    (7812, 6),
    (7813, 3),
    (7814, 0),
    (7815, 1),
    (7816, 5),
    (7817, 7),
    (7818, 2),
    (7819, 6),
    (7820, 3),
    (7821, 0),
    (7822, 1),
    (7823, 5),
    (7824, 7),
    (7825, 2),
    (7826, 6),
    (7827, 3),
    (7828, 0),
    (7829, 1),
    (7830, 5),
    (7831, 7),
    (7832, 2),
    (7833, 6),
    (7834, 3),
    (7835, 0),
    (7836, 1),
    (7837, 5),
    (7838, 7),
    (7839, 2),
    (7840, 6),
    (7841, 3),
    (7842, 4),
    (7843, 0),
    (7844, 1),
    (7845, 5),
    (7846, 7),
    (7847, 2),
    (7848, 6),
    (7849, 3),
    (7850, 0),
    (7851, 1),
    (7852, 5),
    (7853, 7),
    (7854, 2),
    (7855, 6),
    (7856, 3),
    (7857, 0),
    (7858, 1),
    (7859, 5),
    (7860, 7),
    (7861, 2),
    (7862, 6),
    (7863, 3),
    (7864, 0),
    (7865, 1),
    (7866, 5),
    (7867, 7),
    (7868, 2),
    (7869, 6),
    (7870, 3),
    (7871, 0),
    (7872, 1),
    (7873, 5),
    (7874, 7),
    (7875, 2),
    (7876, 6),
    (7877, 3),
    (7878, 0),
    (7879, 1),
    (7880, 5),
    (7881, 7),
    (7882, 2),
    (7883, 6),
    (7884, 3),
    (7885, 0),
    (7886, 1),
    (7887, 5),
    (7888, 7),
    (7889, 2),
    (7890, 6),
    (7891, 3),
    (7892, 0),
    (7893, 1),
    (7894, 5),
    (7895, 7),
    (7896, 2),
    (7897, 6),
    (7898, 3),
    (7899, 0),
    (7900, 1),
    (7901, 5),
    (7902, 7),
    (7903, 2),
    (7904, 6),
    (7905, 3),
    (7906, 4),
    (7907, 0),
    (7908, 1),
    (7909, 5),
    (7910, 7),
    (7911, 2),
    (7912, 6),
    (7913, 3),
    (7914, 0),
    (7915, 1),
    (7916, 5),
    (7917, 7),
    (7918, 2),
    (7919, 6),
    (7920, 3),
    (7921, 0),
    (7922, 1),
    (7923, 5),
    (7924, 7),
    (7925, 2),
    (7926, 6),
    (7927, 3),
    (7928, 0),
    (7929, 1),
    (7930, 5),
    (7931, 7),
    (7932, 2),
    (7933, 6),
    (7934, 3)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData61_allowed (j : Fin 128) :
    (7808 + j.val = 0 ∨ (y422TPathRawData61 j).1 < 7808 + j.val) ∧
      (y422TPathRawData61 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
