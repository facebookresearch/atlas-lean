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
def y422TPathRawData07 : Fin 128 → ℕ × ℕ :=
  ![(895, 8),
    (896, 0),
    (897, 1),
    (898, 2),
    (899, 0),
    (900, 5),
    (16, 8),
    (713, 8),
    (493, 8),
    (844, 7),
    (20, 8),
    (906, 0),
    (907, 1),
    (908, 5),
    (909, 6),
    (910, 0),
    (911, 7),
    (912, 8),
    (913, 0),
    (914, 1),
    (915, 2),
    (916, 5),
    (917, 6),
    (918, 0),
    (919, 7),
    (920, 8),
    (921, 0),
    (922, 1),
    (923, 2),
    (924, 0),
    (925, 5),
    (926, 6),
    (927, 0),
    (928, 7),
    (929, 8),
    (930, 0),
    (931, 1),
    (932, 2),
    (933, 0),
    (934, 5),
    (935, 6),
    (936, 0),
    (937, 7),
    (938, 8),
    (939, 0),
    (940, 1),
    (941, 2),
    (942, 0),
    (943, 5),
    (944, 6),
    (945, 0),
    (946, 7),
    (947, 8),
    (948, 0),
    (949, 1),
    (950, 2),
    (951, 0),
    (952, 5),
    (953, 6),
    (954, 0),
    (955, 7),
    (956, 8),
    (957, 0),
    (958, 1),
    (959, 2),
    (960, 0),
    (961, 5),
    (962, 6),
    (963, 0),
    (964, 7),
    (965, 8),
    (966, 0),
    (967, 1),
    (968, 2),
    (969, 0),
    (970, 5),
    (971, 6),
    (972, 0),
    (973, 7),
    (974, 8),
    (975, 0),
    (976, 1),
    (977, 2),
    (978, 0),
    (979, 5),
    (980, 6),
    (17, 8),
    (379, 8),
    (579, 8),
    (984, 7),
    (985, 8),
    (982, 2),
    (987, 7),
    (988, 8),
    (989, 0),
    (990, 1),
    (991, 2),
    (992, 5),
    (993, 6),
    (994, 0),
    (995, 7),
    (996, 8),
    (997, 0),
    (998, 1),
    (999, 2),
    (1000, 0),
    (1001, 5),
    (1002, 6),
    (1003, 0),
    (1004, 7),
    (1005, 8),
    (1006, 0),
    (1007, 1),
    (1008, 2),
    (1009, 0),
    (1010, 5),
    (1011, 6),
    (1012, 0),
    (1013, 7),
    (1014, 8),
    (1015, 0),
    (1016, 1),
    (1017, 2),
    (1018, 0),
    (1019, 5),
    (1020, 6),
    (1021, 0),
    (1022, 7)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData07_allowed (j : Fin 128) :
    (896 + j.val = 0 ∨ (y422TPathRawData07 j).1 < 896 + j.val) ∧
      (y422TPathRawData07 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
