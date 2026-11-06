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
def y422TPathRawData46 : Fin 128 → ℕ × ℕ :=
  ![(5887, 3),
    (5888, 0),
    (5889, 1),
    (5890, 5),
    (5891, 7),
    (5892, 2),
    (5893, 6),
    (5894, 3),
    (5895, 0),
    (5896, 1),
    (5897, 5),
    (5898, 7),
    (5899, 2),
    (5900, 6),
    (5901, 3),
    (5902, 0),
    (5903, 1),
    (5904, 5),
    (5905, 7),
    (5906, 2),
    (5907, 6),
    (5908, 3),
    (5909, 0),
    (5910, 1),
    (5911, 5),
    (5912, 7),
    (5913, 2),
    (5914, 6),
    (5915, 3),
    (5916, 0),
    (5917, 1),
    (5918, 5),
    (5919, 7),
    (5920, 2),
    (5921, 6),
    (5922, 3),
    (5923, 4),
    (5924, 0),
    (5925, 1),
    (5926, 5),
    (5927, 7),
    (5928, 2),
    (5929, 6),
    (5930, 3),
    (5931, 0),
    (5932, 1),
    (5933, 5),
    (5934, 7),
    (5935, 2),
    (5936, 6),
    (5937, 3),
    (5938, 0),
    (5939, 1),
    (5940, 5),
    (5941, 7),
    (5942, 2),
    (5943, 6),
    (5944, 3),
    (5945, 0),
    (5946, 1),
    (5947, 5),
    (5948, 7),
    (5949, 2),
    (5950, 6),
    (5951, 3),
    (5952, 0),
    (5953, 1),
    (5954, 5),
    (5955, 7),
    (5956, 2),
    (5957, 6),
    (5958, 3),
    (5959, 0),
    (5960, 1),
    (5961, 5),
    (5962, 7),
    (5963, 2),
    (5964, 6),
    (5965, 3),
    (5966, 0),
    (5967, 1),
    (5968, 5),
    (5969, 7),
    (5970, 2),
    (5971, 6),
    (5972, 3),
    (5973, 0),
    (5974, 1),
    (5975, 5),
    (5976, 7),
    (5977, 2),
    (5978, 6),
    (5979, 3),
    (5980, 0),
    (116, 3),
    (116, 6),
    (853, 3),
    (853, 5),
    (853, 6),
    (3465, 3),
    (1429, 3),
    (3465, 6),
    (3465, 7),
    (5715, 4),
    (5715, 5),
    (5715, 6),
    (5715, 7),
    (2478, 6),
    (117, 5),
    (5996, 2),
    (5997, 3),
    (5998, 0),
    (5999, 1),
    (6000, 5),
    (6001, 7),
    (6002, 2),
    (6003, 6),
    (6004, 3),
    (6005, 0),
    (6006, 1),
    (6007, 5),
    (6008, 7),
    (6009, 2),
    (6010, 6),
    (6011, 3),
    (6012, 0),
    (6013, 1),
    (6014, 5)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData46_allowed (j : Fin 128) :
    (5888 + j.val = 0 ∨ (y422TPathRawData46 j).1 < 5888 + j.val) ∧
      (y422TPathRawData46 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
