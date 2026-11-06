/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal chronological right-coset proof data from actual original-source consequences. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawCosetPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Exact literal coset claims and source or chronological right-context moves in this interval. -/
def y422CosetData11 : Fin 128 → Y522RawCosetCertificate :=
  ![
    ⟨[697], [697], [
]⟩,
    ⟨[699, 17], [697], [
      .equation 386 false false
        []
        [17],
      .equation 14 false false
        [697]
        []]⟩,
    ⟨[697, 8, 16], [699], [
      .equation 1 true false
        [697, 8]
        [16],
      .equation 385 false false
        []
        [9, 16],
      .equation 13 false false
        [695, 8]
        [14, 16],
      .equation 1 true false
        [695, 8]
        [14, 16],
      .prior 1405 true [9, 14, 16],
      .equation 3 false false
        [693]
        [8, 0, 14, 16],
      .equation 1 true false
        [693, 8]
        [0, 14, 16],
      .prior 1403 false [0, 14, 16],
      .equation 2 true false
        [693, 0]
        [14, 16],
      .equation 384 true false
        []
        [14, 16],
      .prior 1406 false [14, 16],
      .equation 12 true false
        [695, 14]
        [16],
      .equation 385 true false
        []
        [16],
      .prior 1408 false [16],
      .equation 14 true false
        [697, 16]
        [],
      .equation 386 true false
        []
        []]⟩,
    ⟨[699, 9], [699, 9], [
]⟩,
    ⟨[699], [699], [
]⟩,
    ⟨[699, 9], [699], [
      .prior 1411 false [],
      .equation 386 false false
        []
        [9],
      .equation 15 false false
        [697, 8]
        [16],
      .prior 1410 false [],
      .prior 1412 false []]⟩,
    ⟨[701, 1], [699], [
      .equation 387 false false
        []
        [1],
      .equation 2 false false
        [699]
        []]⟩,
    ⟨[699, 1], [701], [
      .equation 387 true false
        []
        []]⟩,
    ⟨[701, 9], [701, 9], [
]⟩,
    ⟨[701], [701], [
]⟩,
    ⟨[701, 9], [701], [
      .prior 1416 false [],
      .prior 1415 true [9],
      .equation 3 false false
        [699]
        [8, 0],
      .equation 1 true false
        [699, 8]
        [0],
      .prior 1413 false [0],
      .equation 2 true false
        [699, 0]
        [],
      .equation 387 true false
        []
        [],
      .prior 1417 false []]⟩,
    ⟨[703, 3], [701], [
      .equation 388 false false
        []
        [3],
      .equation 4 false false
        [701]
        []]⟩,
    ⟨[701, 3], [703], [
      .equation 388 true false
        []
        []]⟩,
    ⟨[703, 9], [703, 9], [
]⟩,
    ⟨[703], [703], [
]⟩,
    ⟨[703, 9], [703], [
      .prior 1421 false [],
      .prior 1420 true [9],
      .equation 5 false false
        [701]
        [8, 2],
      .equation 1 true false
        [701, 8]
        [2],
      .prior 1418 false [2],
      .equation 4 true false
        [701, 2]
        [],
      .equation 388 true false
        []
        [],
      .prior 1422 false []]⟩,
    ⟨[705, 5], [703], [
      .equation 389 false false
        []
        [5],
      .equation 6 false false
        [703]
        []]⟩,
    ⟨[703, 5], [705], [
      .equation 389 true false
        []
        []]⟩,
    ⟨[705, 9], [705, 9], [
]⟩,
    ⟨[705], [705], [
]⟩,
    ⟨[705, 9], [705], [
      .prior 1426 false [],
      .prior 1425 true [9],
      .equation 7 false false
        [703]
        [8, 4],
      .equation 1 true false
        [703, 8]
        [4],
      .prior 1423 false [4],
      .equation 6 true false
        [703, 4]
        [],
      .equation 389 true false
        []
        [],
      .prior 1427 false []]⟩,
    ⟨[707, 1], [705], [
      .equation 390 false false
        []
        [1],
      .equation 2 false false
        [705]
        []]⟩,
    ⟨[705, 1], [707], [
      .equation 390 true false
        []
        []]⟩,
    ⟨[707], [707], [
]⟩,
    ⟨[709, 11], [707], [
      .equation 391 false false
        []
        [11],
      .equation 8 false false
        [707]
        []]⟩,
    ⟨[709, 9], [709, 9], [
]⟩,
    ⟨[709], [709], [
]⟩,
    ⟨[709, 9], [709], [
      .prior 1433 false [],
      .equation 391 false false
        []
        [9],
      .equation 9 false false
        [707, 8]
        [10],
      .equation 1 true false
        [707, 8]
        [10],
      .prior 1430 true [9, 10],
      .equation 3 false false
        [705]
        [8, 0, 10],
      .equation 1 true false
        [705, 8]
        [0, 10],
      .prior 1428 false [0, 10],
      .equation 2 true false
        [705, 0]
        [10],
      .equation 390 true false
        []
        [10],
      .prior 1431 false [10],
      .equation 8 true false
        [707, 10]
        [],
      .equation 391 true false
        []
        [],
      .prior 1434 false []]⟩,
    ⟨[711, 13], [709], [
      .equation 392 false false
        []
        [13],
      .equation 10 false false
        [709]
        []]⟩,
    ⟨[709, 13], [711], [
      .equation 392 true false
        []
        []]⟩,
    ⟨[709, 8], [709], [
      .equation 1 true false
        [709, 8]
        [],
      .prior 1435 false []]⟩,
    ⟨[711], [711], [
]⟩,
    ⟨[713, 1], [711], [
      .equation 393 false false
        []
        [1],
      .equation 2 false false
        [711]
        []]⟩,
    ⟨[713, 9], [713, 9], [
]⟩,
    ⟨[713], [713], [
]⟩,
    ⟨[713, 9], [713], [
      .prior 1441 false [],
      .equation 393 false false
        []
        [9],
      .equation 3 false false
        [711]
        [8, 0],
      .equation 1 true false
        [711, 8]
        [0],
      .prior 1437 true [9, 0],
      .equation 11 false false
        [709, 8]
        [12, 0],
      .prior 1438 false [12, 0],
      .equation 10 true false
        [709, 12]
        [0],
      .equation 392 true false
        []
        [0],
      .prior 1439 false [0],
      .equation 2 true false
        [711, 0]
        [],
      .equation 393 true false
        []
        [],
      .prior 1442 false []]⟩,
    ⟨[715, 15], [713], [
      .equation 394 false false
        []
        [15],
      .equation 12 false false
        [713]
        []]⟩,
    ⟨[713, 15], [715], [
      .equation 394 true false
        []
        []]⟩,
    ⟨[713, 8], [713], [
      .equation 1 true false
        [713, 8]
        [],
      .prior 1443 false []]⟩,
    ⟨[715, 9], [715, 9], [
]⟩,
    ⟨[715], [715], [
]⟩,
    ⟨[713, 0], [711], [
      .equation 2 true false
        [713, 0]
        [],
      .prior 1440 false []]⟩,
    ⟨[
      713, 0, 12, 10, 0, 4, 2, 0, 16
    ], [699, 16], [
      .prior 1449 false [
        12, 10, 0, 4, 2, 0, 16
      ],
      .equation 10 true false
        [711, 12]
        [10, 0, 4, 2, 0, 16],
      .prior 1436 false [10, 0, 4, 2, 0, 16],
      .equation 8 true false
        [709, 10]
        [0, 4, 2, 0, 16],
      .prior 1432 false [0, 4, 2, 0, 16],
      .equation 2 true false
        [707, 0]
        [4, 2, 0, 16],
      .prior 1429 false [4, 2, 0, 16],
      .equation 6 true false
        [705, 4]
        [2, 0, 16],
      .prior 1424 false [2, 0, 16],
      .equation 4 true false
        [703, 2]
        [0, 16],
      .prior 1419 false [0, 16],
      .equation 2 true false
        [701, 0]
        [16],
      .prior 1414 false [16]]⟩,
    ⟨[
      713, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4
    ], [687, 5], [
      .prior 1450 false [14, 0, 12, 10, 0, 4],
      .equation 14 true false
        [699, 16]
        [14, 0, 12, 10, 0, 4],
      .prior 1409 false [14, 0, 12, 10, 0, 4],
      .equation 12 true false
        [697, 14]
        [0, 12, 10, 0, 4],
      .prior 1407 false [0, 12, 10, 0, 4],
      .equation 2 true false
        [695, 0]
        [12, 10, 0, 4],
      .prior 1404 false [12, 10, 0, 4],
      .equation 10 true false
        [693, 12]
        [10, 0, 4],
      .prior 1399 false [10, 0, 4],
      .equation 8 true false
        [691, 10]
        [0, 4],
      .prior 1394 false [0, 4],
      .equation 2 true false
        [689, 0]
        [4],
      .prior 1389 false [4],
      .equation 6 true false
        [687, 4]
        []]⟩,
    ⟨[
      713, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12
    ], [673], [
      .prior 1451 false [2, 0, 16, 14, 0, 12],
      .prior 1385 false [2, 0, 16, 14, 0, 12],
      .equation 4 true false
        [685, 2]
        [0, 16, 14, 0, 12],
      .prior 1382 false [0, 16, 14, 0, 12],
      .equation 2 true false
        [683, 0]
        [16, 14, 0, 12],
      .prior 1377 false [16, 14, 0, 12],
      .equation 14 true false
        [681, 16]
        [14, 0, 12],
      .prior 1372 false [14, 0, 12],
      .equation 12 true false
        [679, 14]
        [0, 12],
      .prior 1371 false [0, 12],
      .equation 2 true false
        [677, 0]
        [12],
      .prior 1368 false [12],
      .equation 10 true false
        [675, 12]
        [],
      .prior 1364 false []]⟩,
    ⟨[
      713, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16
    ], [661], [
      .prior 1452 false [10, 0, 4, 2, 0, 16],
      .equation 8 true false
        [673, 10]
        [0, 4, 2, 0, 16],
      .prior 1361 false [0, 4, 2, 0, 16],
      .equation 2 true false
        [671, 0]
        [4, 2, 0, 16],
      .prior 1356 false [4, 2, 0, 16],
      .equation 6 true false
        [669, 4]
        [2, 0, 16],
      .prior 1351 false [2, 0, 16],
      .equation 4 true false
        [667, 2]
        [0, 16],
      .equation 370 false false
        []
        [3, 0, 16],
      .equation 4 false false
        [665]
        [0, 16],
      .equation 2 true false
        [665, 0]
        [16],
      .prior 1345 false [16],
      .equation 14 true false
        [663, 16]
        [],
      .prior 1341 false []]⟩,
    ⟨[
      713, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16, 14, 0, 12, 10, 0, 4, 2
    ], [649, 2], [
      .prior 1453 false [
        14, 0, 12, 10, 0, 4, 2
      ],
      .equation 12 true false
        [661, 14]
        [0, 12, 10, 0, 4, 2],
      .prior 1339 false [0, 12, 10, 0, 4, 2],
      .equation 2 true false
        [659, 0]
        [12, 10, 0, 4, 2],
      .prior 1335 false [12, 10, 0, 4, 2],
      .equation 10 true false
        [657, 12]
        [10, 0, 4, 2],
      .prior 1330 false [10, 0, 4, 2],
      .equation 8 true false
        [655, 10]
        [0, 4, 2],
      .equation 364 false false
        []
        [11, 0, 4, 2],
      .equation 8 false false
        [653]
        [0, 4, 2],
      .equation 2 true false
        [653, 0]
        [4, 2],
      .equation 363 false false
        []
        [1, 4, 2],
      .equation 2 false false
        [651]
        [4, 2],
      .equation 6 true false
        [651, 4]
        [2],
      .prior 1322 false [2]]⟩,
    ⟨[
      713, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16,
      14, 0, 12
    ], [637], [
      .prior 1454 false [0, 16, 14, 0, 12],
      .equation 4 true false
        [649, 2]
        [0, 16, 14, 0, 12],
      .equation 361 false false
        []
        [3, 0, 16, 14, 0, 12],
      .equation 4 false false
        [647]
        [0, 16, 14, 0, 12],
      .equation 2 true false
        [647, 0]
        [16, 14, 0, 12],
      .prior 1318 false [16, 14, 0, 12],
      .equation 14 true false
        [645, 16]
        [14, 0, 12],
      .prior 1313 false [14, 0, 12],
      .equation 12 true false
        [643, 14]
        [0, 12],
      .prior 1309 false [0, 12],
      .equation 2 true false
        [641, 0]
        [12],
      .equation 357 false false
        []
        [1, 12],
      .equation 2 false false
        [639]
        [12],
      .equation 10 true false
        [639, 12]
        [],
      .prior 1303 false []]⟩,
    ⟨[
      713, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16,
      14, 0, 12, 10, 0, 4, 2, 0, 16, 14
    ], [627, 14], [
      .prior 1455 false [
        10, 0, 4, 2, 0, 16, 14
      ],
      .equation 8 true false
        [637, 10]
        [0, 4, 2, 0, 16, 14],
      .prior 1298 false [0, 4, 2, 0, 16, 14],
      .equation 2 true false
        [635, 0]
        [4, 2, 0, 16, 14],
      .prior 1293 false [4, 2, 0, 16, 14],
      .equation 6 true false
        [633, 4]
        [2, 0, 16, 14],
      .prior 1286 false [2, 0, 16, 14],
      .equation 4 true false
        [631, 2]
        [0, 16, 14],
      .prior 1279 false [0, 16, 14],
      .equation 2 true false
        [629, 0]
        [16, 14],
      .prior 1274 false [16, 14],
      .equation 14 true false
        [629, 16]
        [14],
      .prior 1270 false [14]]⟩,
    ⟨[
      713, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16,
      14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2
    ], [615, 3], [
      .prior 1456 false [0, 12, 10, 0, 4, 2],
      .equation 12 true false
        [627, 14]
        [0, 12, 10, 0, 4, 2],
      .prior 1263 false [0, 12, 10, 0, 4, 2],
      .equation 2 true false
        [625, 0]
        [12, 10, 0, 4, 2],
      .prior 1253 false [12, 10, 0, 4, 2],
      .equation 10 true false
        [623, 12]
        [10, 0, 4, 2],
      .prior 1243 false [10, 0, 4, 2],
      .equation 8 true false
        [621, 10]
        [0, 4, 2],
      .prior 1223 false [0, 4, 2],
      .equation 2 true false
        [619, 0]
        [4, 2],
      .prior 1211 false [4, 2],
      .equation 6 true false
        [617, 4]
        [2],
      .prior 1199 false [2],
      .equation 4 true false
        [615, 2]
        []]⟩,
    ⟨[
      713, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16,
      14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10
    ], [609], [
      .prior 1457 false [0, 16, 14, 0, 12, 10],
      .prior 1171 false [0, 16, 14, 0, 12, 10],
      .equation 2 true false
        [613, 0]
        [16, 14, 0, 12, 10],
      .prior 1162 false [16, 14, 0, 12, 10],
      .equation 14 true false
        [613, 16]
        [14, 0, 12, 10],
      .prior 1170 false [14, 0, 12, 10],
      .equation 12 true false
        [613, 14]
        [0, 12, 10],
      .prior 1158 false [0, 12, 10],
      .equation 2 true false
        [217, 0]
        [12, 10],
      .prior 552 false [12, 10],
      .equation 10 true false
        [215, 12]
        [10],
      .prior 1156 false [10],
      .equation 8 true false
        [611, 10]
        [],
      .prior 1139 false []]⟩,
    ⟨[
      713, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16,
      14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16, 14
    ], [29], [
      .prior 1458 false [0, 4, 2, 0, 16, 14],
      .equation 2 true false
        [609, 0]
        [4, 2, 0, 16, 14],
      .prior 1126 false [4, 2, 0, 16, 14],
      .equation 6 true false
        [609, 4]
        [2, 0, 16, 14],
      .prior 1130 false [2, 0, 16, 14],
      .equation 4 true false
        [609, 2]
        [0, 16, 14],
      .prior 1128 false [0, 16, 14],
      .equation 2 true false
        [609, 0]
        [16, 14],
      .prior 1126 false [16, 14],
      .equation 14 true false
        [609, 16]
        [14],
      .prior 1122 false [14],
      .equation 12 true false
        [211, 14]
        [],
      .prior 266 false []]⟩,
    ⟨[
      713, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16,
      14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0
    ], [29, 0], [
      .prior 1459 false [
        0, 12, 10, 0, 4, 2, 0
      ],
      .equation 2 true false
        [29, 0]
        [12, 10, 0, 4, 2, 0],
      .prior 68 false [12, 10, 0, 4, 2, 0],
      .equation 10 true false
        [27, 12]
        [10, 0, 4, 2, 0],
      .prior 63 false [10, 0, 4, 2, 0],
      .equation 8 true false
        [27, 10]
        [0, 4, 2, 0],
      .prior 61 false [0, 4, 2, 0],
      .equation 2 true false
        [27, 0]
        [4, 2, 0],
      .equation 38 true false
        []
        [4, 2, 0],
      .equation 6 true false
        [29, 4]
        [2, 0],
      .prior 74 false [2, 0],
      .equation 4 true false
        [29, 2]
        [0],
      .prior 72 false [0]]⟩,
    ⟨[
      713, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16,
      14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16,
      14, 0, 12, 10, 0
    ], [31, 1], [
      .prior 1460 false [16, 14, 0, 12, 10, 0],
      .equation 2 true false
        [29, 0]
        [16, 14, 0, 12, 10, 0],
      .prior 68 false [16, 14, 0, 12, 10, 0],
      .equation 14 true false
        [27, 16]
        [14, 0, 12, 10, 0],
      .prior 67 false [14, 0, 12, 10, 0],
      .equation 12 true false
        [27, 14]
        [0, 12, 10, 0],
      .prior 65 false [0, 12, 10, 0],
      .equation 2 true false
        [27, 0]
        [12, 10, 0],
      .equation 38 true false
        []
        [12, 10, 0],
      .equation 10 true false
        [29, 12]
        [10, 0],
      .prior 80 false [10, 0],
      .equation 8 true false
        [29, 10]
        [0],
      .equation 42 true false
        []
        [0],
      .equation 2 true false
        [31, 0]
        []]⟩,
    ⟨[
      713, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16,
      14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16,
      14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0
    ], [205], [
      .prior 1461 false [4, 2, 0, 16, 14, 0],
      .prior 87 false [4, 2, 0, 16, 14, 0],
      .equation 6 true false
        [31, 4]
        [2, 0, 16, 14, 0],
      .prior 91 false [2, 0, 16, 14, 0],
      .equation 4 true false
        [31, 2]
        [0, 16, 14, 0],
      .prior 89 false [0, 16, 14, 0],
      .equation 2 true false
        [31, 0]
        [16, 14, 0],
      .prior 87 false [16, 14, 0],
      .equation 14 true false
        [31, 16]
        [14, 0],
      .prior 97 false [14, 0],
      .equation 12 true false
        [31, 14]
        [0],
      .equation 45 true false
        []
        [0],
      .equation 2 true false
        [33, 0]
        [],
      .prior 273 false []]⟩,
    ⟨[
      713, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16,
      14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4,
      2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16,
      14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12,
      10, 0, 4, 2, 0
    ], [187], [
      .prior 1462 false [12, 10, 0, 4, 2, 0],
      .prior 298 false [12, 10, 0, 4, 2, 0],
      .equation 10 true false
        [203, 12]
        [10, 0, 4, 2, 0],
      .prior 230 false [10, 0, 4, 2, 0],
      .prior 309 false [10, 0, 4, 2, 0],
      .equation 8 true false
        [37, 10]
        [0, 4, 2, 0],
      .prior 319 false [0, 4, 2, 0],
      .equation 2 true false
        [195, 0]
        [4, 2, 0],
      .prior 327 false [4, 2, 0],
      .equation 6 true false
        [195, 4]
        [2, 0],
      .prior 330 false [2, 0],
      .equation 4 true false
        [195, 2]
        [0],
      .prior 226 false [0],
      .prior 347 false [0],
      .equation 2 true false
        [41, 0]
        [],
      .prior 339 false [],
      .prior 374 false []]⟩,
    ⟨[715, 17], [715, 17], [
]⟩,
    ⟨[187], [187], [
]⟩,
    ⟨[715, 17], [187], [
      .prior 1464 false [],
      .prior 1445 true [17],
      .equation 198 false false
        [
          713, 0, 12, 10, 0, 4, 2, 0
        ]
        [
          16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0,
          12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0,
          4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0,
          16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0,
          12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0,
          4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0,
          16, 14, 0, 12, 10, 0, 4, 2, 0
        ],
      .prior 1463 false [],
      .prior 1465 false []]⟩,
    ⟨[187, 17], [715], [
      .prior 1466 true [17],
      .equation 14 false false
        [715]
        []]⟩,
    ⟨[715, 17], [187], [
      .prior 1464 false [],
      .prior 1466 false []]⟩,
    ⟨[715, 3], [715, 3], [
]⟩,
    ⟨[715, 3], [715], [
      .prior 1469 false [],
      .prior 1467 true [3],
      .prior 377 true [17, 3],
      .prior 1468 true [3, 17, 3],
      .equation 37 false false
        [715, 2]
        [3],
      .prior 1448 false []]⟩,
    ⟨[715, 7], [715, 7], [
]⟩,
    ⟨[715, 7], [715], [
      .prior 1471 false [],
      .prior 1467 true [7],
      .prior 375 true [17, 7],
      .prior 1468 true [7, 17, 7],
      .equation 24 false false
        [715, 6]
        [7],
      .prior 1448 false []]⟩,
    ⟨[715, 11], [715, 11], [
]⟩,
    ⟨[715, 11], [715], [
      .prior 1473 false [],
      .prior 1467 true [11],
      .prior 378 true [17, 11],
      .prior 1468 true [11, 17, 11],
      .equation 44 false false
        [715, 10]
        [11],
      .prior 1448 false []]⟩,
    ⟨[715, 13], [715, 13], [
]⟩,
    ⟨[715, 13], [715], [
      .prior 1475 false [],
      .prior 1467 true [13],
      .prior 376 true [17, 13],
      .equation 123 false false
        []
        [17, 13],
      .prior 1468 true [13, 17, 13],
      .equation 141 false false
        [715, 12]
        [13],
      .prior 1448 false []]⟩,
    ⟨[715, 3], [715], [
      .prior 1469 false [],
      .prior 1470 false []]⟩,
    ⟨[715, 14], [713], [
      .equation 12 true false
        [715, 14]
        [],
      .prior 1444 false []]⟩,
    ⟨[713, 3], [713, 3], [
]⟩,
    ⟨[713, 3], [713], [
      .prior 1479 false [],
      .prior 1444 true [3],
      .prior 1477 true [15, 3],
      .equation 36 false false
        [715]
        [14],
      .prior 1478 false [],
      .prior 1442 false []]⟩,
    ⟨[715, 7], [715], [
      .prior 1471 false [],
      .prior 1472 false []]⟩,
    ⟨[713, 7], [713, 7], [
]⟩,
    ⟨[713, 7], [713], [
      .prior 1482 false [],
      .prior 1444 true [7],
      .prior 1481 true [15, 7],
      .equation 23 false false
        [715]
        [14],
      .prior 1478 false [],
      .prior 1442 false []]⟩,
    ⟨[715, 11], [715], [
      .prior 1473 false [],
      .prior 1474 false []]⟩,
    ⟨[713, 11], [713, 11], [
]⟩,
    ⟨[713, 11], [713], [
      .prior 1485 false [],
      .prior 1444 true [11],
      .prior 1484 true [15, 11],
      .equation 136 false false
        [715]
        [14],
      .prior 1478 false [],
      .prior 1442 false []]⟩,
    ⟨[715, 13], [715], [
      .prior 1475 false [],
      .prior 1476 false []]⟩,
    ⟨[713, 13], [713, 13], [
]⟩,
    ⟨[713, 13], [713], [
      .prior 1488 false [],
      .prior 1444 true [13],
      .prior 1487 true [15, 13],
      .equation 138 false false
        [715]
        [14],
      .prior 1478 false [],
      .prior 1442 false []]⟩,
    ⟨[713, 7], [713], [
      .prior 1482 false [],
      .prior 1483 false []]⟩,
    ⟨[713, 13], [713], [
      .prior 1488 false [],
      .prior 1489 false []]⟩,
    ⟨[709, 1], [709, 1], [
]⟩,
    ⟨[709, 1], [713], [
      .prior 1492 false [],
      .prior 1436 true [1],
      .prior 1440 true [13, 1],
      .prior 1491 true [1, 13, 1],
      .equation 40 false false
        [713, 0]
        [1],
      .prior 1442 false []]⟩,
    ⟨[713, 1], [711], [
      .prior 1440 false []]⟩,
    ⟨[711], [709], [
      .prior 1494 true [],
      .prior 1493 true [1],
      .equation 2 false false
        [709]
        []]⟩,
    ⟨[711], [709], [
      .prior 1495 false []]⟩,
    ⟨[709, 7], [709], [
      .prior 1495 true [7],
      .prior 1440 true [7],
      .prior 1490 true [1, 7],
      .equation 18 false false
        [713, 0]
        [],
      .prior 1449 false [],
      .prior 1439 false [],
      .prior 1496 false []]⟩,
    ⟨[709, 7], [709], [
      .prior 1497 false []]⟩,
    ⟨[709, 1], [713], [
      .prior 1492 false [],
      .prior 1493 false []]⟩,
    ⟨[705, 11], [705, 11], [
]⟩,
    ⟨[705, 11], [709], [
      .prior 1500 false [],
      .prior 1429 true [11],
      .prior 1432 true [1, 11],
      .prior 1496 true [11, 1, 11],
      .prior 1440 true [11, 1, 11],
      .prior 1486 true [1, 11, 1, 11],
      .prior 1499 true [11, 1, 11, 1, 11],
      .equation 43 false false
        [709]
        [],
      .prior 1434 false []]⟩,
    ⟨[709, 11], [707], [
      .prior 1432 false []]⟩,
    ⟨[707], [705], [
      .prior 1502 true [],
      .prior 1501 true [11],
      .equation 8 false false
        [705]
        []]⟩,
    ⟨[707], [705], [
      .prior 1503 false []]⟩,
    ⟨[705, 7], [705], [
      .prior 1503 true [7],
      .prior 1432 true [7],
      .prior 1498 true [11, 7],
      .equation 21 false false
        [709]
        [10],
      .equation 8 true false
        [709, 10]
        [],
      .prior 1432 false [],
      .prior 1431 false [],
      .prior 1504 false []]⟩,
    ⟨[705, 5], [703], [
      .prior 1424 false []]⟩,
    ⟨[703, 1], [703, 1], [
]⟩,
    ⟨[703, 1], [703], [
      .prior 1507 false [],
      .prior 1506 true [1],
      .equation 26 false false
        [705, 0]
        [4],
      .equation 2 true false
        [705, 0]
        [4],
      .equation 390 true false
        []
        [4],
      .prior 1504 false [4],
      .equation 6 true false
        [705, 4]
        [],
      .prior 1424 false [],
      .prior 1422 false []]⟩,
    ⟨[703, 1], [703], [
      .prior 1507 false [],
      .prior 1508 false []]⟩,
    ⟨[699, 3], [699, 3], [
]⟩,
    ⟨[699, 3], [699], [
      .prior 1510 false [],
      .prior 1414 true [3],
      .prior 1419 true [1, 3],
      .prior 1509 true [3, 1, 3],
      .equation 39 false false
        [703]
        [2, 0],
      .equation 4 true false
        [703, 2]
        [0],
      .prior 1419 false [0],
      .equation 2 true false
        [701, 0]
        [],
      .prior 1414 false [],
      .prior 1412 false []]⟩,
    ⟨[699, 3], [699], [
      .prior 1510 false [],
      .prior 1511 false []]⟩,
    ⟨[699, 16], [697], [
      .equation 14 true false
        [699, 16]
        [],
      .prior 1409 false []]⟩,
    ⟨[697, 3], [697, 3], [
]⟩,
    ⟨[719, 9], [485], [
      .equation 396 false false
        []
        [9],
      .equation 5 false false
        [717]
        [8, 2],
      .equation 1 true false
        [717, 8]
        [2],
      .equation 395 false false
        []
        [9, 2],
      .equation 3 false false
        [479]
        [8, 0, 2],
      .equation 1 true false
        [479, 8]
        [0, 2],
      .equation 277 true false
        []
        [0, 2],
      .equation 2 true false
        [481, 0]
        [2],
      .equation 278 true false
        []
        [2],
      .equation 4 true false
        [483, 2]
        [],
      .equation 279 true false
        []
        []]⟩,
    ⟨[723, 8, 4], [491], [
      .equation 1 true false
        [723, 8]
        [4],
      .equation 398 false false
        []
        [9, 4],
      .equation 13 false false
        [721, 8]
        [14, 4],
      .equation 1 true false
        [721, 8]
        [14, 4],
      .equation 397 false false
        []
        [9, 14, 4],
      .equation 9 false false
        [719, 8]
        [10, 14, 4],
      .equation 1 true false
        [719, 8]
        [10, 14, 4],
      .prior 1515 false [10, 14, 4],
      .equation 8 true false
        [485, 10]
        [14, 4],
      .equation 280 true false
        []
        [14, 4],
      .equation 12 true false
        [487, 14]
        [4],
      .equation 281 true false
        []
        [4],
      .equation 6 true false
        [489, 4]
        [],
      .equation 282 true false
        []
        []]⟩,
    ⟨[743, 13], [741], [
      .equation 408 false false
        []
        [13],
      .equation 10 false false
        [741]
        []]⟩,
    ⟨[745, 7], [743], [
      .equation 409 false false
        []
        [7],
      .equation 17 false false
        [743]
        []]⟩,
    ⟨[749, 3], [747], [
      .equation 411 false false
        []
        [3],
      .equation 4 false false
        [747]
        []]⟩,
    ⟨[751, 11], [749], [
      .equation 412 false false
        []
        [11],
      .equation 8 false false
        [749]
        []]⟩,
    ⟨[755, 5], [753], [
      .equation 414 false false
        []
        [5],
      .equation 6 false false
        [753]
        []]⟩,
    ⟨[757, 13], [755], [
      .equation 415 false false
        []
        [13],
      .equation 10 false false
        [755]
        []]⟩,
    ⟨[759, 7], [757], [
      .equation 416 false false
        []
        [7],
      .equation 17 false false
        [757]
        []]⟩,
    ⟨[761, 1], [759], [
      .equation 417 false false
        []
        [1],
      .equation 2 false false
        [759]
        []]⟩,
    ⟨[763, 3], [761], [
      .equation 418 false false
        []
        [3],
      .equation 4 false false
        [761]
        []]⟩,
    ⟨[765, 11], [763], [
      .equation 419 false false
        []
        [11],
      .equation 8 false false
        [763]
        []]⟩,
    ⟨[767, 15], [765], [
      .equation 420 false false
        []
        [15],
      .equation 12 false false
        [765]
        []]⟩,
    ⟨[769, 5], [767], [
      .equation 421 false false
        []
        [5],
      .equation 6 false false
        [767]
        []]⟩,
    ⟨[771, 13], [769], [
      .equation 422 false false
        []
        [13],
      .equation 10 false false
        [769]
        []]⟩,
    ⟨[773, 7], [771], [
      .equation 423 false false
        []
        [7],
      .equation 17 false false
        [771]
        []]⟩,
    ⟨[775, 1], [773], [
      .equation 424 false false
        []
        [1],
      .equation 2 false false
        [773]
        []]⟩,
    ⟨[777, 3], [775], [
      .equation 425 false false
        []
        [3],
      .equation 4 false false
        [775]
        []]⟩,
    ⟨[779, 11], [777], [
      .equation 426 false false
        []
        [11],
      .equation 8 false false
        [777]
        []]⟩,
    ⟨[781, 15], [779], [
      .equation 427 false false
        []
        [15],
      .equation 12 false false
        [779]
        []]⟩,
    ⟨[783, 5], [781], [
      .equation 428 false false
        []
        [5],
      .equation 6 false false
        [781]
        []]⟩]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
