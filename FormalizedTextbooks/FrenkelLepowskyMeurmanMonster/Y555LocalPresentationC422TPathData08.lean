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
def y422TPathRawData08 : Fin 128 → ℕ × ℕ :=
  ![(1023, 8),
    (1024, 0),
    (1025, 1),
    (1026, 2),
    (1027, 0),
    (1028, 5),
    (1029, 6),
    (1030, 0),
    (1031, 7),
    (1032, 8),
    (1033, 0),
    (1034, 1),
    (1035, 2),
    (1036, 0),
    (1037, 5),
    (1038, 6),
    (1039, 0),
    (1040, 7),
    (1041, 8),
    (1042, 0),
    (1043, 1),
    (1044, 2),
    (1045, 0),
    (1046, 5),
    (1047, 6),
    (1048, 0),
    (1049, 7),
    (1050, 8),
    (1051, 0),
    (1052, 1),
    (1053, 2),
    (1054, 0),
    (1055, 5),
    (1056, 6),
    (494, 8),
    (375, 8),
    (19, 8),
    (1060, 7),
    (1061, 8),
    (787, 8),
    (904, 7),
    (1064, 0),
    (1065, 1),
    (1066, 2),
    (1067, 5),
    (1068, 6),
    (1069, 0),
    (1070, 7),
    (1071, 8),
    (1072, 1),
    (1073, 2),
    (1074, 0),
    (1075, 5),
    (1076, 6),
    (1077, 0),
    (1078, 7),
    (1079, 8),
    (1080, 0),
    (1081, 1),
    (1082, 2),
    (1083, 0),
    (1084, 5),
    (1085, 6),
    (1086, 0),
    (1087, 7),
    (1088, 8),
    (1089, 0),
    (1090, 1),
    (1091, 2),
    (1092, 0),
    (1093, 5),
    (1094, 6),
    (1095, 0),
    (1096, 7),
    (1097, 8),
    (1098, 0),
    (1099, 1),
    (1100, 2),
    (1101, 0),
    (1102, 5),
    (1103, 6),
    (1104, 0),
    (1105, 7),
    (1106, 8),
    (1107, 0),
    (1108, 1),
    (1109, 2),
    (1110, 0),
    (1111, 5),
    (1112, 6),
    (1113, 0),
    (1114, 7),
    (1115, 8),
    (1116, 0),
    (1117, 1),
    (1118, 2),
    (1119, 0),
    (1120, 5),
    (1121, 6),
    (1122, 0),
    (1123, 7),
    (1124, 8),
    (1125, 0),
    (1126, 1),
    (1127, 2),
    (1128, 0),
    (1129, 5),
    (1130, 6),
    (77, 8),
    (386, 8),
    (1132, 5),
    (1134, 6),
    (1135, 7),
    (1136, 0),
    (1137, 1),
    (1138, 2),
    (1139, 5),
    (1140, 6),
    (1141, 0),
    (1142, 7),
    (1143, 8),
    (1144, 1),
    (1145, 2),
    (1146, 0),
    (1147, 5),
    (1148, 6),
    (1149, 0),
    (1150, 7)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData08_allowed (j : Fin 128) :
    (1024 + j.val = 0 ∨ (y422TPathRawData08 j).1 < 1024 + j.val) ∧
      (y422TPathRawData08 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
