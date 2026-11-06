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
def y422TPathRawData62 : Fin 128 → ℕ × ℕ :=
  ![(7935, 0),
    (7936, 1),
    (7937, 5),
    (7938, 7),
    (7939, 2),
    (7940, 6),
    (7941, 3),
    (7942, 0),
    (7943, 1),
    (7944, 5),
    (7945, 7),
    (7946, 2),
    (7947, 6),
    (7948, 3),
    (7949, 0),
    (7950, 1),
    (7951, 5),
    (7952, 7),
    (7953, 2),
    (7954, 6),
    (7955, 3),
    (7956, 0),
    (7957, 1),
    (7958, 5),
    (7959, 7),
    (7960, 2),
    (7961, 6),
    (7962, 3),
    (7963, 0),
    (7964, 1),
    (7965, 5),
    (7966, 7),
    (7429, 1),
    (7429, 2),
    (7429, 3),
    (7429, 5),
    (321, 2),
    (7519, 3),
    (7519, 8),
    (2367, 3),
    (7975, 2),
    (7976, 3),
    (7710, 4),
    (7710, 6),
    (7710, 8),
    (7156, 5),
    (7156, 8),
    (7968, 2),
    (7983, 0),
    (7984, 5),
    (7985, 6),
    (7986, 0),
    (7987, 7),
    (7988, 8),
    (7989, 1),
    (7990, 2),
    (7991, 0),
    (7992, 5),
    (7993, 6),
    (7994, 7),
    (7995, 8),
    (7996, 0),
    (7997, 1),
    (7998, 2),
    (7999, 0),
    (8000, 5),
    (8001, 6),
    (8002, 0),
    (8003, 7),
    (8004, 8),
    (8005, 0),
    (8006, 1),
    (8007, 2),
    (8008, 0),
    (8009, 5),
    (8010, 6),
    (8011, 0),
    (8012, 7),
    (8013, 8),
    (8014, 0),
    (8015, 1),
    (8016, 2),
    (8017, 0),
    (8018, 5),
    (8019, 6),
    (8020, 0),
    (8021, 7),
    (8022, 8),
    (8023, 0),
    (8024, 1),
    (8025, 2),
    (8026, 0),
    (8027, 5),
    (8028, 6),
    (8029, 0),
    (8030, 7),
    (8031, 8),
    (8032, 0),
    (8033, 1),
    (8034, 2),
    (8035, 0),
    (8036, 5),
    (8037, 6),
    (8038, 0),
    (8039, 7),
    (8040, 8),
    (8041, 0),
    (8042, 1),
    (8043, 2),
    (8044, 0),
    (8045, 5),
    (8046, 6),
    (8047, 0),
    (8048, 7),
    (8049, 8),
    (8050, 0),
    (8051, 1),
    (8052, 2),
    (8053, 0),
    (8054, 5),
    (8055, 6),
    (8056, 0),
    (8057, 7),
    (8058, 8),
    (8059, 0),
    (8060, 1),
    (8061, 2),
    (8062, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData62_allowed (j : Fin 128) :
    (7936 + j.val = 0 ∨ (y422TPathRawData62 j).1 < 7936 + j.val) ∧
      (y422TPathRawData62 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
