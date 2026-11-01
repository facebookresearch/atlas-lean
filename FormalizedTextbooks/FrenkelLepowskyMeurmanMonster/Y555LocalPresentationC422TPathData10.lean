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
def y422TPathRawData10 : Fin 128 → ℕ × ℕ :=
  ![(1279, 2),
    (1280, 0),
    (1281, 5),
    (1282, 6),
    (1283, 0),
    (1284, 7),
    (1285, 8),
    (1286, 0),
    (1287, 1),
    (1288, 2),
    (1289, 0),
    (1290, 5),
    (1291, 6),
    (1292, 0),
    (1293, 7),
    (1294, 8),
    (1295, 0),
    (1296, 1),
    (1297, 2),
    (1298, 0),
    (1299, 5),
    (1300, 6),
    (1301, 0),
    (1302, 7),
    (1303, 8),
    (1304, 0),
    (1305, 1),
    (1306, 2),
    (1307, 0),
    (1308, 5),
    (1309, 6),
    (1310, 0),
    (1311, 7),
    (1312, 8),
    (1313, 0),
    (1314, 1),
    (1315, 2),
    (1316, 0),
    (1317, 5),
    (1318, 6),
    (1319, 0),
    (1320, 7),
    (1321, 8),
    (1322, 0),
    (1323, 1),
    (1324, 2),
    (1325, 0),
    (1326, 5),
    (1327, 6),
    (1328, 0),
    (1329, 7),
    (1330, 8),
    (1331, 0),
    (1332, 1),
    (1333, 2),
    (1334, 0),
    (1335, 5),
    (1336, 6),
    (1337, 0),
    (1338, 7),
    (1339, 8),
    (1340, 0),
    (1341, 1),
    (1342, 2),
    (1343, 0),
    (1344, 5),
    (1345, 6),
    (252, 8),
    (908, 7),
    (1056, 1),
    (1349, 2),
    (1350, 0),
    (1351, 5),
    (1352, 6),
    (1353, 0),
    (1354, 7),
    (1355, 8),
    (1356, 0),
    (1357, 1),
    (1358, 2),
    (1359, 0),
    (1360, 5),
    (1361, 6),
    (1362, 0),
    (1363, 7),
    (1364, 8),
    (1365, 0),
    (1366, 1),
    (1367, 2),
    (1368, 0),
    (1369, 5),
    (1370, 6),
    (1371, 0),
    (1372, 7),
    (1373, 8),
    (1374, 0),
    (1375, 1),
    (1376, 2),
    (1377, 0),
    (1378, 5),
    (1379, 6),
    (1380, 0),
    (1381, 7),
    (1382, 8),
    (1383, 0),
    (1384, 1),
    (1385, 2),
    (1386, 0),
    (1387, 5),
    (1388, 6),
    (1389, 0),
    (1390, 7),
    (1391, 8),
    (1392, 0),
    (1393, 1),
    (1394, 2),
    (1395, 0),
    (1396, 5),
    (1397, 6),
    (1398, 0),
    (1399, 7),
    (1400, 8),
    (1401, 0),
    (1402, 1),
    (1403, 2),
    (1404, 0),
    (1405, 5),
    (1406, 6)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every nonroot parent is strictly earlier, and every source generator has its actual bound.
/-- Exact chronological parent and source-generator bounds for this whole finite interval. -/
theorem y422TPathRawData10_allowed (j : Fin 128) :
    (1280 + j.val = 0 ∨ (y422TPathRawData10 j).1 < 1280 + j.val) ∧
      (y422TPathRawData10 j).2 < 9 := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
