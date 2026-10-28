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
def y422TPathRawData54 : Fin 128 → ℕ × ℕ :=
  ![(6911, 7),
    (6912, 8),
    (6913, 0),
    (6914, 1),
    (6915, 2),
    (6916, 0),
    (6917, 5),
    (6918, 6),
    (6919, 0),
    (6920, 7),
    (6921, 8),
    (6922, 0),
    (6923, 1),
    (6924, 2),
    (6925, 0),
    (6926, 5),
    (6927, 6),
    (6928, 0),
    (6929, 7),
    (6930, 8),
    (6931, 0),
    (6932, 1),
    (6933, 2),
    (6934, 0),
    (6935, 5),
    (6936, 6),
    (6937, 0),
    (6938, 7),
    (6939, 8),
    (6940, 0),
    (6941, 1),
    (6942, 2),
    (6943, 0),
    (6944, 5),
    (6945, 6),
    (6946, 0),
    (6947, 7),
    (6948, 8),
    (6949, 0),
    (6950, 1),
    (6951, 2),
    (6952, 0),
    (6953, 5),
    (6954, 6),
    (6955, 0),
    (6956, 7),
    (6957, 8),
    (6958, 0),
    (6959, 1),
    (6960, 2),
    (6961, 0),
    (6962, 5),
    (6963, 6),
    (6964, 0),
    (6965, 7),
    (6966, 8),
    (6967, 0),
    (6968, 1),
    (6969, 2),
    (6970, 0),
    (6971, 5),
    (6972, 6),
    (6973, 0),
    (6903, 3),
    (6975, 0),
    (6976, 1),
    (6977, 7),
    (6978, 2),
    (6979, 3),
    (6980, 0),
    (6981, 1),
    (6982, 5),
    (6983, 7),
    (6984, 2),
    (6985, 6),
    (6986, 3),
    (6987, 0),
    (6988, 1),
    (6989, 5),
    (6990, 7),
    (6991, 2),
    (6992, 6),
    (6993, 3),
    (6994, 0),
    (6995, 1),
    (6996, 5),
    (6997, 7),
    (6998, 2),
    (6999, 6),
    (7000, 3),
    (7001, 0),
    (7002, 1),
    (7003, 5),
    (7004, 7),
    (7005, 2),
    (7006, 6),
    (7007, 3),
    (7008, 0),
    (7009, 1),
    (7010, 5),
    (7011, 7),
    (7012, 2),
    (7013, 6),
    (7014, 3),
    (7015, 0),
    (7016, 1),
    (7017, 5),
    (7018, 7),
    (7019, 2),
    (7020, 6),
    (7021, 3),
    (7022, 0),
    (7023, 1),
    (7024, 5),
    (7025, 7),
    (7026, 2),
    (7027, 6),
    (7028, 3),
    (7029, 4),
    (7030, 0),
    (7031, 1),
    (7032, 5),
    (7033, 7),
    (7034, 2),
    (7035, 6),
    (7036, 3),
    (7037, 0),
    (7038, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData54_allowed (j : Fin 128) :
    (6912 + j.val = 0 ∨ (y422TPathRawData54 j).1 < 6912 + j.val) ∧
      (y422TPathRawData54 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
