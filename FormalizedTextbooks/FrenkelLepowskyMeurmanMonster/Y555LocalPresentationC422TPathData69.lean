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
def y422TPathRawData69 : Fin 128 → ℕ × ℕ :=
  ![(8831, 6),
    (8832, 3),
    (8833, 0),
    (8834, 1),
    (8835, 5),
    (8836, 7),
    (8837, 2),
    (8838, 6),
    (8839, 3),
    (8840, 0),
    (8841, 1),
    (8842, 5),
    (8843, 7),
    (8844, 2),
    (8845, 6),
    (8846, 3),
    (8847, 0),
    (8848, 1),
    (8849, 5),
    (8850, 7),
    (8851, 2),
    (8852, 6),
    (8853, 3),
    (8854, 0),
    (8855, 1),
    (8856, 5),
    (8857, 7),
    (8858, 2),
    (8859, 6),
    (8860, 3),
    (8861, 0),
    (8862, 1),
    (8863, 5),
    (8864, 7),
    (8865, 2),
    (8866, 6),
    (8867, 3),
    (8868, 4),
    (8869, 0),
    (8870, 1),
    (8871, 5),
    (8872, 7),
    (8873, 2),
    (8874, 6),
    (8875, 3),
    (8876, 0),
    (8877, 1),
    (8878, 5),
    (8879, 7),
    (8880, 2),
    (8881, 6),
    (8882, 3),
    (8883, 0),
    (8884, 1),
    (8885, 5),
    (8886, 7),
    (8887, 2),
    (8888, 6),
    (8889, 3),
    (8890, 0),
    (8891, 1),
    (8892, 5),
    (8893, 7),
    (8894, 2),
    (8895, 6),
    (8896, 3),
    (8897, 0),
    (8898, 1),
    (8899, 5),
    (8900, 7),
    (8901, 2),
    (8902, 6),
    (8903, 3),
    (8904, 0),
    (8905, 1),
    (8906, 5),
    (8907, 7),
    (8908, 2),
    (8909, 6),
    (8910, 3),
    (8911, 0),
    (8912, 1),
    (8913, 5),
    (8914, 7),
    (8915, 2),
    (8916, 6),
    (8917, 3),
    (8918, 0),
    (8919, 1),
    (8920, 5),
    (8921, 7),
    (8922, 2),
    (8923, 6),
    (8924, 3),
    (8925, 0),
    (8926, 1),
    (8927, 5),
    (8928, 7),
    (8929, 2),
    (8930, 6),
    (8931, 3),
    (8932, 4),
    (8933, 0),
    (8934, 1),
    (8935, 5),
    (8936, 7),
    (8937, 2),
    (8938, 6),
    (8939, 3),
    (8940, 0),
    (8941, 1),
    (8942, 5),
    (8943, 7),
    (8944, 2),
    (8945, 6),
    (8946, 3),
    (8947, 0),
    (8948, 1),
    (8949, 5),
    (8950, 7),
    (8951, 2),
    (8952, 6),
    (8953, 3),
    (8954, 0),
    (8955, 1),
    (8956, 5),
    (8957, 7),
    (8958, 2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData69_allowed (j : Fin 128) :
    (8832 + j.val = 0 ∨ (y422TPathRawData69 j).1 < 8832 + j.val) ∧
      (y422TPathRawData69 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
