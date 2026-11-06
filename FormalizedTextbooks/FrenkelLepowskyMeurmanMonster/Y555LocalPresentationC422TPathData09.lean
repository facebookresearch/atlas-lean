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
def y422TPathRawData09 : Fin 128 → ℕ × ℕ :=
  ![(1151, 8),
    (1152, 0),
    (1153, 1),
    (1154, 2),
    (1155, 0),
    (1156, 5),
    (1157, 6),
    (1158, 0),
    (1159, 7),
    (1160, 8),
    (1161, 0),
    (1162, 1),
    (1163, 2),
    (1164, 0),
    (1165, 5),
    (1166, 6),
    (1167, 0),
    (1168, 7),
    (1169, 8),
    (1170, 0),
    (1171, 1),
    (1172, 2),
    (1173, 0),
    (1174, 5),
    (1175, 6),
    (1176, 0),
    (1177, 7),
    (1178, 8),
    (1179, 0),
    (1180, 1),
    (1181, 2),
    (1182, 0),
    (1183, 5),
    (1184, 6),
    (1185, 0),
    (1186, 7),
    (1187, 8),
    (1188, 0),
    (1189, 1),
    (1190, 2),
    (1191, 0),
    (1192, 5),
    (1193, 6),
    (1194, 0),
    (1195, 7),
    (1196, 8),
    (1197, 0),
    (1198, 1),
    (1199, 2),
    (1200, 0),
    (1201, 5),
    (1202, 6),
    (371, 8),
    (68, 8),
    (1205, 5),
    (1206, 0),
    (1207, 7),
    (1208, 0),
    (1209, 1),
    (1210, 2),
    (1211, 0),
    (1212, 5),
    (1213, 6),
    (1214, 0),
    (1215, 7),
    (1216, 8),
    (1217, 0),
    (1218, 1),
    (1219, 2),
    (1220, 0),
    (1221, 5),
    (1222, 6),
    (1223, 0),
    (1224, 7),
    (1225, 8),
    (1226, 0),
    (1227, 1),
    (1228, 2),
    (1229, 0),
    (1230, 5),
    (1231, 6),
    (1232, 0),
    (1233, 7),
    (1234, 8),
    (1235, 0),
    (1236, 1),
    (1237, 2),
    (1238, 0),
    (1239, 5),
    (1240, 6),
    (1241, 0),
    (1242, 7),
    (1243, 8),
    (1244, 0),
    (1245, 1),
    (1246, 2),
    (1247, 0),
    (1248, 5),
    (1249, 6),
    (1250, 0),
    (1251, 7),
    (1252, 8),
    (1253, 0),
    (1254, 1),
    (1255, 2),
    (1256, 0),
    (1257, 5),
    (1258, 6),
    (1259, 0),
    (1260, 7),
    (1261, 8),
    (1262, 0),
    (1263, 1),
    (1264, 2),
    (1265, 0),
    (1266, 5),
    (1267, 6),
    (1268, 0),
    (1269, 7),
    (1270, 8),
    (1271, 0),
    (254, 8),
    (74, 8),
    (907, 7),
    (1135, 2),
    (1274, 7),
    (1277, 0),
    (1278, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData09_allowed (j : Fin 128) :
    (1152 + j.val = 0 ∨ (y422TPathRawData09 j).1 < 1152 + j.val) ∧
      (y422TPathRawData09 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
