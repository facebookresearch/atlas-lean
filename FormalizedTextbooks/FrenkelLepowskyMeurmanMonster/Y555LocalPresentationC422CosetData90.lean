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
def y422CosetData90 : Fin 128 → Y522RawCosetCertificate :=
  ![
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6
    ], [6575], [
      .prior 11519 false [4, 14, 10, 2, 0, 6],
      .prior 11504 false [4, 14, 10, 2, 0, 6],
      .equation 6 true false
        [6587, 4]
        [14, 10, 2, 0, 6],
      .prior 11503 false [14, 10, 2, 0, 6],
      .equation 12 true false
        [6585, 14]
        [10, 2, 0, 6],
      .prior 11502 false [10, 2, 0, 6],
      .equation 8 true false
        [6583, 10]
        [2, 0, 6],
      .prior 11501 false [2, 0, 6],
      .equation 4 true false
        [6581, 2]
        [0, 6],
      .prior 11500 false [0, 6],
      .equation 2 true false
        [6579, 0]
        [6],
      .prior 11499 false [6],
      .equation 17 true false
        [6577, 6]
        [],
      .prior 11498 false []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0
    ], [6563], [
      .prior 11520 false [12, 4, 14, 10, 2, 0],
      .equation 10 true false
        [6575, 12]
        [4, 14, 10, 2, 0],
      .prior 11497 false [4, 14, 10, 2, 0],
      .equation 6 true false
        [6573, 4]
        [14, 10, 2, 0],
      .prior 11496 false [14, 10, 2, 0],
      .equation 12 true false
        [6571, 14]
        [10, 2, 0],
      .prior 11495 false [10, 2, 0],
      .equation 8 true false
        [6569, 10]
        [2, 0],
      .prior 11494 false [2, 0],
      .equation 4 true false
        [6567, 2]
        [0],
      .prior 11493 false [0],
      .equation 2 true false
        [6565, 0]
        [],
      .prior 11492 false []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0
    ], [6551, 0], [
      .prior 11521 false [
        6, 12, 4, 14, 10, 2, 0
      ],
      .equation 17 true false
        [6563, 6]
        [12, 4, 14, 10, 2, 0],
      .prior 11491 false [12, 4, 14, 10, 2, 0],
      .equation 10 true false
        [6561, 12]
        [4, 14, 10, 2, 0],
      .equation 3317 false false
        []
        [13, 4, 14, 10, 2, 0],
      .equation 10 false false
        [6559]
        [4, 14, 10, 2, 0],
      .equation 6 true false
        [6559, 4]
        [14, 10, 2, 0],
      .prior 11490 false [14, 10, 2, 0],
      .equation 12 true false
        [6557, 14]
        [10, 2, 0],
      .equation 3315 false false
        []
        [15, 10, 2, 0],
      .equation 12 false false
        [6555]
        [10, 2, 0],
      .equation 8 true false
        [6555, 10]
        [2, 0],
      .prior 11489 false [2, 0],
      .equation 4 true false
        [6553, 2]
        [0],
      .prior 11488 false [0]]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2
    ], [6539, 3], [
      .prior 11522 false [6, 12, 4, 14, 10, 2],
      .equation 2 true false
        [6551, 0]
        [6, 12, 4, 14, 10, 2],
      .prior 11487 false [6, 12, 4, 14, 10, 2],
      .equation 17 true false
        [6549, 6]
        [12, 4, 14, 10, 2],
      .prior 11486 false [12, 4, 14, 10, 2],
      .equation 10 true false
        [6547, 12]
        [4, 14, 10, 2],
      .equation 3310 false false
        []
        [13, 4, 14, 10, 2],
      .equation 10 false false
        [6545]
        [4, 14, 10, 2],
      .equation 6 true false
        [6545, 4]
        [14, 10, 2],
      .equation 3309 false false
        []
        [5, 14, 10, 2],
      .equation 6 false false
        [6543]
        [14, 10, 2],
      .equation 12 true false
        [6543, 14]
        [10, 2],
      .equation 3308 false false
        []
        [15, 10, 2],
      .equation 12 false false
        [6541]
        [10, 2],
      .equation 8 true false
        [6541, 10]
        [2],
      .equation 3307 false false
        []
        [11, 2],
      .equation 8 false false
        [6539]
        [2],
      .equation 4 true false
        [6539, 2]
        []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14
    ], [6527], [
      .prior 11523 false [0, 6, 12, 4, 14],
      .equation 3306 false false
        []
        [3, 0, 6, 12, 4, 14],
      .equation 4 false false
        [6537]
        [0, 6, 12, 4, 14],
      .equation 2 true false
        [6537, 0]
        [6, 12, 4, 14],
      .equation 3305 false false
        []
        [1, 6, 12, 4, 14],
      .equation 2 false false
        [6535]
        [6, 12, 4, 14],
      .equation 17 true false
        [6535, 6]
        [12, 4, 14],
      .equation 3304 false false
        []
        [7, 12, 4, 14],
      .equation 17 false false
        [6533]
        [12, 4, 14],
      .equation 10 true false
        [6533, 12]
        [4, 14],
      .equation 3303 false false
        []
        [13, 4, 14],
      .equation 10 false false
        [6531]
        [4, 14],
      .equation 6 true false
        [6531, 4]
        [14],
      .equation 3302 false false
        []
        [5, 14],
      .equation 6 false false
        [6529]
        [14],
      .equation 12 true false
        [6529, 14]
        [],
      .equation 3301 false false
        []
        [15],
      .equation 12 false false
        [6527]
        []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12
    ], [6515], [
      .prior 11524 false [10, 2, 0, 8, 6, 12],
      .equation 8 true false
        [6527, 10]
        [2, 0, 8, 6, 12],
      .equation 3300 false false
        []
        [11, 2, 0, 8, 6, 12],
      .equation 8 false false
        [6525]
        [2, 0, 8, 6, 12],
      .equation 4 true false
        [6525, 2]
        [0, 8, 6, 12],
      .equation 3299 false false
        []
        [3, 0, 8, 6, 12],
      .equation 4 false false
        [6523]
        [0, 8, 6, 12],
      .equation 2 true false
        [6523, 0]
        [8, 6, 12],
      .equation 3298 false false
        []
        [1, 8, 6, 12],
      .equation 2 false false
        [6521]
        [8, 6, 12],
      .equation 1 true false
        [6521, 8]
        [6, 12],
      .equation 3297 false false
        []
        [9, 6, 12],
      .equation 1 false false
        [6519]
        [6, 12],
      .equation 17 true false
        [6519, 6]
        [12],
      .prior 11485 false [12],
      .equation 10 true false
        [6517, 12]
        [],
      .prior 11484 false []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12
    ], [6503, 12], [
      .prior 11525 false [
        4, 14, 10, 2, 0, 6, 12
      ],
      .equation 6 true false
        [6515, 4]
        [14, 10, 2, 0, 6, 12],
      .prior 11483 false [14, 10, 2, 0, 6, 12],
      .equation 12 true false
        [6513, 14]
        [10, 2, 0, 6, 12],
      .prior 11482 false [10, 2, 0, 6, 12],
      .equation 8 true false
        [6511, 10]
        [2, 0, 6, 12],
      .prior 11481 false [2, 0, 6, 12],
      .equation 4 true false
        [6509, 2]
        [0, 6, 12],
      .prior 11480 false [0, 6, 12],
      .equation 2 true false
        [6507, 0]
        [6, 12],
      .prior 11479 false [6, 12],
      .equation 17 true false
        [6505, 6]
        [12],
      .prior 11478 false [12]]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6
    ], [6491, 7], [
      .prior 11526 false [4, 14, 10, 2, 0, 6],
      .equation 10 true false
        [6503, 12]
        [4, 14, 10, 2, 0, 6],
      .prior 11477 false [4, 14, 10, 2, 0, 6],
      .equation 6 true false
        [6501, 4]
        [14, 10, 2, 0, 6],
      .prior 11476 false [14, 10, 2, 0, 6],
      .equation 12 true false
        [6499, 14]
        [10, 2, 0, 6],
      .prior 11475 false [10, 2, 0, 6],
      .equation 8 true false
        [6497, 10]
        [2, 0, 6],
      .prior 11474 false [2, 0, 6],
      .equation 4 true false
        [6495, 2]
        [0, 6],
      .equation 3284 false false
        []
        [3, 0, 6],
      .equation 4 false false
        [6493]
        [0, 6],
      .equation 2 true false
        [6493, 0]
        [6],
      .equation 3283 false false
        []
        [1, 6],
      .equation 2 false false
        [6491]
        [6],
      .equation 17 true false
        [6491, 6]
        []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2
    ], [6479], [
      .prior 11527 false [12, 4, 14, 10, 2],
      .equation 3282 false false
        []
        [7, 12, 4, 14, 10, 2],
      .equation 17 false false
        [6489]
        [12, 4, 14, 10, 2],
      .equation 10 true false
        [6489, 12]
        [4, 14, 10, 2],
      .equation 3281 false false
        []
        [13, 4, 14, 10, 2],
      .equation 10 false false
        [6487]
        [4, 14, 10, 2],
      .equation 6 true false
        [6487, 4]
        [14, 10, 2],
      .prior 11473 false [14, 10, 2],
      .equation 12 true false
        [6485, 14]
        [10, 2],
      .equation 3279 false false
        []
        [15, 10, 2],
      .equation 12 false false
        [6483]
        [10, 2],
      .equation 8 true false
        [6483, 10]
        [2],
      .equation 3278 false false
        []
        [11, 2],
      .equation 8 false false
        [6481]
        [2],
      .equation 4 true false
        [6481, 2]
        [],
      .equation 3277 false false
        []
        [3],
      .equation 4 false false
        [6479]
        []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10
    ], [6467], [
      .prior 11528 false [0, 6, 12, 4, 14, 10],
      .equation 2 true false
        [6479, 0]
        [6, 12, 4, 14, 10],
      .equation 3276 false false
        []
        [1, 6, 12, 4, 14, 10],
      .equation 2 false false
        [6477]
        [6, 12, 4, 14, 10],
      .equation 17 true false
        [6477, 6]
        [12, 4, 14, 10],
      .prior 11472 false [12, 4, 14, 10],
      .equation 10 true false
        [6475, 12]
        [4, 14, 10],
      .equation 3274 false false
        []
        [13, 4, 14, 10],
      .equation 10 false false
        [6473]
        [4, 14, 10],
      .equation 6 true false
        [6473, 4]
        [14, 10],
      .prior 11471 false [14, 10],
      .equation 12 true false
        [6471, 14]
        [10],
      .equation 3272 false false
        []
        [15, 10],
      .equation 12 false false
        [6469]
        [10],
      .equation 8 true false
        [6469, 10]
        [],
      .prior 11470 false []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10
    ], [6455, 10], [
      .prior 11529 false [
        2, 0, 6, 12, 4, 14, 10
      ],
      .equation 4 true false
        [6467, 2]
        [0, 6, 12, 4, 14, 10],
      .prior 11469 false [0, 6, 12, 4, 14, 10],
      .equation 2 true false
        [6465, 0]
        [6, 12, 4, 14, 10],
      .prior 11468 false [6, 12, 4, 14, 10],
      .equation 17 true false
        [6463, 6]
        [12, 4, 14, 10],
      .equation 3268 false false
        []
        [7, 12, 4, 14, 10],
      .equation 17 false false
        [6461]
        [12, 4, 14, 10],
      .equation 10 true false
        [6461, 12]
        [4, 14, 10],
      .prior 11467 false [4, 14, 10],
      .equation 6 true false
        [6459, 4]
        [14, 10],
      .equation 3266 false false
        []
        [5, 14, 10],
      .equation 6 false false
        [6457]
        [14, 10],
      .equation 12 true false
        [6457, 14]
        [10],
      .prior 11466 false [10]]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4
    ], [6443], [
      .prior 11530 false [2, 0, 6, 12, 4],
      .equation 8 true false
        [6455, 10]
        [2, 0, 6, 12, 4],
      .equation 3264 false false
        []
        [11, 2, 0, 6, 12, 4],
      .equation 8 false false
        [6453]
        [2, 0, 6, 12, 4],
      .equation 4 true false
        [6453, 2]
        [0, 6, 12, 4],
      .equation 3263 false false
        []
        [3, 0, 6, 12, 4],
      .equation 4 false false
        [6451]
        [0, 6, 12, 4],
      .equation 2 true false
        [6451, 0]
        [6, 12, 4],
      .equation 3262 false false
        []
        [1, 6, 12, 4],
      .equation 2 false false
        [6449]
        [6, 12, 4],
      .equation 17 true false
        [6449, 6]
        [12, 4],
      .equation 3261 false false
        []
        [7, 12, 4],
      .equation 17 false false
        [6447]
        [12, 4],
      .equation 10 true false
        [6447, 12]
        [4],
      .equation 3260 false false
        []
        [13, 4],
      .equation 10 false false
        [6445]
        [4],
      .equation 6 true false
        [6445, 4]
        [],
      .equation 3259 false false
        []
        [5],
      .equation 6 false false
        [6443]
        []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12
    ], [6431], [
      .prior 11531 false [14, 10, 2, 0, 6, 12],
      .equation 12 true false
        [6443, 14]
        [10, 2, 0, 6, 12],
      .equation 3258 false false
        []
        [15, 10, 2, 0, 6, 12],
      .equation 12 false false
        [6441]
        [10, 2, 0, 6, 12],
      .equation 8 true false
        [6441, 10]
        [2, 0, 6, 12],
      .equation 3257 false false
        []
        [11, 2, 0, 6, 12],
      .equation 8 false false
        [6439]
        [2, 0, 6, 12],
      .equation 4 true false
        [6439, 2]
        [0, 6, 12],
      .prior 11465 false [0, 6, 12],
      .equation 2 true false
        [6437, 0]
        [6, 12],
      .prior 11464 false [6, 12],
      .equation 17 true false
        [6435, 6]
        [12],
      .equation 3254 false false
        []
        [7, 12],
      .equation 17 false false
        [6433]
        [12],
      .equation 10 true false
        [6433, 12]
        [],
      .equation 3253 false false
        []
        [13],
      .equation 10 false false
        [6431]
        []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12
    ], [6419, 12], [
      .prior 11532 false [
        4, 14, 10, 2, 0, 6, 12
      ],
      .equation 6 true false
        [6431, 4]
        [14, 10, 2, 0, 6, 12],
      .prior 11463 false [14, 10, 2, 0, 6, 12],
      .equation 12 true false
        [6429, 14]
        [10, 2, 0, 6, 12],
      .equation 3251 false false
        []
        [15, 10, 2, 0, 6, 12],
      .equation 12 false false
        [6427]
        [10, 2, 0, 6, 12],
      .equation 8 true false
        [6427, 10]
        [2, 0, 6, 12],
      .prior 11462 false [2, 0, 6, 12],
      .equation 4 true false
        [6425, 2]
        [0, 6, 12],
      .prior 11461 false [0, 6, 12],
      .equation 2 true false
        [6423, 0]
        [6, 12],
      .prior 11460 false [6, 12],
      .equation 17 true false
        [6421, 6]
        [12],
      .prior 11459 false [12]]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6
    ], [6407, 7], [
      .prior 11533 false [4, 14, 10, 2, 0, 6],
      .equation 10 true false
        [6419, 12]
        [4, 14, 10, 2, 0, 6],
      .prior 11458 false [4, 14, 10, 2, 0, 6],
      .equation 6 true false
        [6417, 4]
        [14, 10, 2, 0, 6],
      .prior 11457 false [14, 10, 2, 0, 6],
      .equation 12 true false
        [6415, 14]
        [10, 2, 0, 6],
      .prior 11456 false [10, 2, 0, 6],
      .equation 8 true false
        [6413, 10]
        [2, 0, 6],
      .prior 11455 false [2, 0, 6],
      .equation 4 true false
        [6411, 2]
        [0, 6],
      .prior 11454 false [0, 6],
      .equation 2 true false
        [6409, 0]
        [6],
      .prior 11453 false [6],
      .equation 17 true false
        [6407, 6]
        []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0
    ], [6393], [
      .prior 11534 false [12, 4, 14, 10, 2, 0],
      .prior 11452 false [12, 4, 14, 10, 2, 0],
      .equation 10 true false
        [6405, 12]
        [4, 14, 10, 2, 0],
      .equation 3239 false false
        []
        [13, 4, 14, 10, 2, 0],
      .equation 10 false false
        [6403]
        [4, 14, 10, 2, 0],
      .equation 6 true false
        [6403, 4]
        [14, 10, 2, 0],
      .equation 3238 false false
        []
        [5, 14, 10, 2, 0],
      .equation 6 false false
        [6401]
        [14, 10, 2, 0],
      .equation 12 true false
        [6401, 14]
        [10, 2, 0],
      .equation 3237 false false
        []
        [15, 10, 2, 0],
      .equation 12 false false
        [6399]
        [10, 2, 0],
      .equation 8 true false
        [6399, 10]
        [2, 0],
      .equation 3236 false false
        []
        [11, 2, 0],
      .equation 8 false false
        [6397]
        [2, 0],
      .equation 4 true false
        [6397, 2]
        [0],
      .equation 3235 false false
        []
        [3, 0],
      .equation 4 false false
        [6395]
        [0],
      .equation 2 true false
        [6395, 0]
        [],
      .equation 3234 false false
        []
        [1],
      .equation 2 false false
        [6393]
        []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 8, 6, 12, 4, 14, 10
    ], [6381], [
      .prior 11535 false [8, 6, 12, 4, 14, 10],
      .equation 1 true false
        [6393, 8]
        [6, 12, 4, 14, 10],
      .prior 11451 false [6, 12, 4, 14, 10],
      .equation 17 true false
        [6391, 6]
        [12, 4, 14, 10],
      .equation 3232 false false
        []
        [7, 12, 4, 14, 10],
      .equation 17 false false
        [6389]
        [12, 4, 14, 10],
      .equation 10 true false
        [6389, 12]
        [4, 14, 10],
      .equation 3231 false false
        []
        [13, 4, 14, 10],
      .equation 10 false false
        [6387]
        [4, 14, 10],
      .equation 6 true false
        [6387, 4]
        [14, 10],
      .equation 3230 false false
        []
        [5, 14, 10],
      .equation 6 false false
        [6385]
        [14, 10],
      .equation 12 true false
        [6385, 14]
        [10],
      .equation 3229 false false
        []
        [15, 10],
      .equation 12 false false
        [6383]
        [10],
      .equation 8 true false
        [6383, 10]
        [],
      .equation 3228 false false
        []
        [11],
      .equation 8 false false
        [6381]
        []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14
    ], [6369], [
      .prior 11536 false [2, 0, 6, 12, 4, 14],
      .equation 4 true false
        [6381, 2]
        [0, 6, 12, 4, 14],
      .equation 3227 false false
        []
        [3, 0, 6, 12, 4, 14],
      .equation 4 false false
        [6379]
        [0, 6, 12, 4, 14],
      .equation 2 true false
        [6379, 0]
        [6, 12, 4, 14],
      .equation 3226 false false
        []
        [1, 6, 12, 4, 14],
      .equation 2 false false
        [6377]
        [6, 12, 4, 14],
      .equation 17 true false
        [6377, 6]
        [12, 4, 14],
      .equation 3225 false false
        []
        [7, 12, 4, 14],
      .equation 17 false false
        [6375]
        [12, 4, 14],
      .equation 10 true false
        [6375, 12]
        [4, 14],
      .equation 3224 false false
        []
        [13, 4, 14],
      .equation 10 false false
        [6373]
        [4, 14],
      .equation 6 true false
        [6373, 4]
        [14],
      .equation 3223 false false
        []
        [5, 14],
      .equation 6 false false
        [6371]
        [14],
      .equation 12 true false
        [6371, 14]
        [],
      .equation 3222 false false
        []
        [15],
      .equation 12 false false
        [6369]
        []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4
    ], [6357], [
      .prior 11537 false [10, 2, 0, 6, 12, 4],
      .equation 8 true false
        [6369, 10]
        [2, 0, 6, 12, 4],
      .equation 3221 false false
        []
        [11, 2, 0, 6, 12, 4],
      .equation 8 false false
        [6367]
        [2, 0, 6, 12, 4],
      .equation 4 true false
        [6367, 2]
        [0, 6, 12, 4],
      .equation 3220 false false
        []
        [3, 0, 6, 12, 4],
      .equation 4 false false
        [6365]
        [0, 6, 12, 4],
      .equation 2 true false
        [6365, 0]
        [6, 12, 4],
      .equation 3219 false false
        []
        [1, 6, 12, 4],
      .equation 2 false false
        [6363]
        [6, 12, 4],
      .equation 17 true false
        [6363, 6]
        [12, 4],
      .equation 3218 false false
        []
        [7, 12, 4],
      .equation 17 false false
        [6361]
        [12, 4],
      .equation 10 true false
        [6361, 12]
        [4],
      .equation 3217 false false
        []
        [13, 4],
      .equation 10 false false
        [6359]
        [4],
      .equation 6 true false
        [6359, 4]
        [],
      .equation 3216 false false
        []
        [5],
      .equation 6 false false
        [6357]
        []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12
    ], [6345], [
      .prior 11538 false [14, 10, 2, 0, 6, 12],
      .equation 12 true false
        [6357, 14]
        [10, 2, 0, 6, 12],
      .equation 3215 false false
        []
        [15, 10, 2, 0, 6, 12],
      .equation 12 false false
        [6355]
        [10, 2, 0, 6, 12],
      .equation 8 true false
        [6355, 10]
        [2, 0, 6, 12],
      .equation 3214 false false
        []
        [11, 2, 0, 6, 12],
      .equation 8 false false
        [6353]
        [2, 0, 6, 12],
      .equation 4 true false
        [6353, 2]
        [0, 6, 12],
      .equation 3213 false false
        []
        [3, 0, 6, 12],
      .equation 4 false false
        [6351]
        [0, 6, 12],
      .equation 2 true false
        [6351, 0]
        [6, 12],
      .equation 3212 false false
        []
        [1, 6, 12],
      .equation 2 false false
        [6349]
        [6, 12],
      .equation 17 true false
        [6349, 6]
        [12],
      .equation 3211 false false
        []
        [7, 12],
      .equation 17 false false
        [6347]
        [12],
      .equation 10 true false
        [6347, 12]
        [],
      .equation 3210 false false
        []
        [13],
      .equation 10 false false
        [6345]
        []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6
    ], [6333], [
      .prior 11539 false [4, 14, 10, 2, 0, 6],
      .equation 6 true false
        [6345, 4]
        [14, 10, 2, 0, 6],
      .equation 3209 false false
        []
        [5, 14, 10, 2, 0, 6],
      .equation 6 false false
        [6343]
        [14, 10, 2, 0, 6],
      .equation 12 true false
        [6343, 14]
        [10, 2, 0, 6],
      .equation 3208 false false
        []
        [15, 10, 2, 0, 6],
      .equation 12 false false
        [6341]
        [10, 2, 0, 6],
      .equation 8 true false
        [6341, 10]
        [2, 0, 6],
      .equation 3207 false false
        []
        [11, 2, 0, 6],
      .equation 8 false false
        [6339]
        [2, 0, 6],
      .equation 4 true false
        [6339, 2]
        [0, 6],
      .prior 11450 false [0, 6],
      .equation 2 true false
        [6337, 0]
        [6],
      .equation 3205 false false
        []
        [1, 6],
      .equation 2 false false
        [6335]
        [6],
      .equation 17 true false
        [6335, 6]
        [],
      .equation 3204 false false
        []
        [7],
      .equation 17 false false
        [6333]
        []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6
    ], [6321, 6], [
      .prior 11540 false [
        12, 4, 14, 10, 2, 0, 6
      ],
      .equation 10 true false
        [6333, 12]
        [4, 14, 10, 2, 0, 6],
      .prior 11449 false [4, 14, 10, 2, 0, 6],
      .equation 6 true false
        [6331, 4]
        [14, 10, 2, 0, 6],
      .prior 11448 false [14, 10, 2, 0, 6],
      .equation 12 true false
        [6329, 14]
        [10, 2, 0, 6],
      .prior 11447 false [10, 2, 0, 6],
      .equation 8 true false
        [6327, 10]
        [2, 0, 6],
      .equation 3200 false false
        []
        [11, 2, 0, 6],
      .equation 8 false false
        [6325]
        [2, 0, 6],
      .equation 4 true false
        [6325, 2]
        [0, 6],
      .prior 11446 false [0, 6],
      .equation 2 true false
        [6323, 0]
        [6],
      .equation 3198 false false
        []
        [1, 6],
      .equation 2 false false
        [6321]
        [6]]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2
    ], [6309], [
      .prior 11541 false [12, 4, 14, 10, 2],
      .equation 17 true false
        [6321, 6]
        [12, 4, 14, 10, 2],
      .equation 3197 false false
        []
        [7, 12, 4, 14, 10, 2],
      .equation 17 false false
        [6319]
        [12, 4, 14, 10, 2],
      .equation 10 true false
        [6319, 12]
        [4, 14, 10, 2],
      .prior 11445 false [4, 14, 10, 2],
      .equation 6 true false
        [6317, 4]
        [14, 10, 2],
      .equation 3195 false false
        []
        [5, 14, 10, 2],
      .equation 6 false false
        [6315]
        [14, 10, 2],
      .equation 12 true false
        [6315, 14]
        [10, 2],
      .prior 11441 false [10, 2],
      .equation 8 true false
        [6313, 10]
        [2],
      .prior 11436 false [2],
      .equation 4 true false
        [6311, 2]
        [],
      .prior 11430 false []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2
    ], [6303, 2], [
      .prior 11542 false [
        0, 6, 12, 4, 14, 10, 2
      ],
      .equation 2 true false
        [6309, 0]
        [6, 12, 4, 14, 10, 2],
      .prior 11423 false [6, 12, 4, 14, 10, 2],
      .equation 17 true false
        [6307, 6]
        [12, 4, 14, 10, 2],
      .prior 11418 false [12, 4, 14, 10, 2],
      .equation 10 true false
        [6307, 12]
        [4, 14, 10, 2],
      .prior 11420 false [4, 14, 10, 2],
      .equation 6 true false
        [6307, 4]
        [14, 10, 2],
      .prior 11414 false [14, 10, 2],
      .equation 12 true false
        [6305, 14]
        [10, 2],
      .prior 11410 false [10, 2],
      .equation 8 true false
        [6305, 10]
        [2],
      .prior 11403 false [2]]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10
    ], [5975, 11], [
      .prior 11543 false [0, 6, 12, 4, 14, 10],
      .equation 4 true false
        [6303, 2]
        [0, 6, 12, 4, 14, 10],
      .prior 11396 false [0, 6, 12, 4, 14, 10],
      .equation 2 true false
        [6301, 0]
        [6, 12, 4, 14, 10],
      .prior 11386 false [6, 12, 4, 14, 10],
      .equation 17 true false
        [6299, 6]
        [12, 4, 14, 10],
      .prior 11379 false [12, 4, 14, 10],
      .equation 10 true false
        [4609, 12]
        [4, 14, 10],
      .prior 8857 false [4, 14, 10],
      .equation 6 true false
        [4607, 4]
        [14, 10],
      .prior 9515 true [5, 14, 10],
      .equation 6 false false
        [4961]
        [14, 10],
      .prior 10226 false [14, 10],
      .equation 12 true false
        [4839, 14]
        [10],
      .prior 11117 false [10],
      .prior 11119 false [10],
      .equation 8 true false
        [5975, 10]
        []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14
    ], [223], [
      .prior 11544 false [2, 0, 6, 12, 4, 14],
      .prior 11123 false [2, 0, 6, 12, 4, 14],
      .equation 4 true false
        [5187, 2]
        [0, 6, 12, 4, 14],
      .prior 10138 false [0, 6, 12, 4, 14],
      .equation 2 true false
        [1565, 0]
        [6, 12, 4, 14],
      .equation 820 true false
        []
        [6, 12, 4, 14],
      .equation 17 true false
        [1567, 6]
        [12, 4, 14],
      .prior 4625 false [12, 4, 14],
      .equation 10 true false
        [1567, 12]
        [4, 14],
      .prior 4621 false [4, 14],
      .equation 6 true false
        [1567, 4]
        [14],
      .prior 4637 false [14],
      .equation 12 true false
        [1453, 14]
        [],
      .prior 4321 false []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 8, 6, 12
    ], [2145], [
      .prior 11545 false [10, 2, 0, 8, 6, 12],
      .equation 8 true false
        [223, 10]
        [2, 0, 8, 6, 12],
      .prior 590 false [2, 0, 8, 6, 12],
      .equation 4 true false
        [221, 2]
        [0, 8, 6, 12],
      .prior 586 false [0, 8, 6, 12],
      .equation 2 true false
        [221, 0]
        [8, 6, 12],
      .prior 584 false [8, 6, 12],
      .equation 1 true false
        [221, 8]
        [6, 12],
      .prior 589 false [6, 12],
      .equation 17 true false
        [221, 6]
        [12],
      .prior 5432 false [12],
      .equation 10 true false
        [1827, 12]
        [],
      .prior 6124 false []]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 8, 6, 12, 4, 14,
      10, 2, 0, 6, 12
    ], [4857, 12], [
      .prior 11546 false [
        4, 14, 10, 2, 0, 6, 12
      ],
      .equation 6 true false
        [2145, 4]
        [14, 10, 2, 0, 6, 12],
      .prior 6116 false [14, 10, 2, 0, 6, 12],
      .equation 12 true false
        [2145, 14]
        [10, 2, 0, 6, 12],
      .equation 2143 true false
        []
        [10, 2, 0, 6, 12],
      .equation 8 true false
        [4213, 10]
        [2, 0, 6, 12],
      .prior 8443 false [2, 0, 6, 12],
      .equation 4 true false
        [4213, 2]
        [0, 6, 12],
      .prior 8439 false [0, 6, 12],
      .equation 2 true false
        [4213, 0]
        [6, 12],
      .equation 2144 true false
        []
        [6, 12],
      .equation 17 true false
        [4215, 6]
        [12],
      .prior 9356 false [12]]⟩,
    ⟨[
      6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 8,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 8, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6
    ], [309, 7], [
      .prior 11547 false [4, 14, 10, 2, 0, 6],
      .equation 10 true false
        [4857, 12]
        [4, 14, 10, 2, 0, 6],
      .prior 9361 false [4, 14, 10, 2, 0, 6],
      .equation 6 true false
        [619, 4]
        [14, 10, 2, 0, 6],
      .prior 1214 false [14, 10, 2, 0, 6],
      .equation 12 true false
        [313, 14]
        [10, 2, 0, 6],
      .prior 883 false [10, 2, 0, 6],
      .equation 8 true false
        [313, 10]
        [2, 0, 6],
      .prior 794 false [2, 0, 6],
      .equation 4 true false
        [311, 2]
        [0, 6],
      .prior 1196 false [0, 6],
      .equation 2 true false
        [311, 0]
        [6],
      .prior 789 false [6],
      .equation 17 true false
        [309, 6]
        []]⟩,
    ⟨[6615, 13], [6615, 13], [
]⟩,
    ⟨[6615, 13], [309], [
      .prior 11549 false [],
      .equation 3344 false false
        []
        [13],
      .equation 135 false false
        [
          6613, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
          6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
          2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
          14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0
        ]
        [
          8, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
          10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
          4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
          6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
          2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
          14, 10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0,
          6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
          2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
          14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
          12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
          0, 6, 12, 4, 14, 10, 2, 0, 8, 6, 12, 4,
          14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6
        ],
      .prior 11548 false [],
      .prior 905 false [],
      .prior 787 false []]⟩,
    ⟨[309, 13], [6615], [
      .prior 11550 true [13],
      .equation 10 false false
        [6615]
        []]⟩,
    ⟨[6615, 5], [6613], [
      .prior 11517 false []]⟩,
    ⟨[307, 13], [625], [
      .prior 1260 false []]⟩,
    ⟨[6613], [625], [
      .equation 10 true false
        [6613]
        [],
      .prior 11552 true [13, 13],
      .equation 29 false false
        [6615]
        [12, 4, 13],
      .equation 10 true false
        [6615, 12]
        [4, 13],
      .prior 11550 false [4, 13],
      .equation 6 true false
        [309, 4]
        [13],
      .prior 784 false [13],
      .prior 782 false [13],
      .prior 11553 false []]⟩,
    ⟨[625, 5], [6615], [
      .prior 11554 true [5],
      .equation 3344 true false
        []
        []]⟩,
    ⟨[6613], [625], [
      .prior 11554 false []]⟩,
    ⟨[6607, 1], [1813, 1], [
      .prior 11514 true [1],
      .prior 11515 true [3, 1],
      .prior 11516 true [11, 3, 1],
      .prior 11556 false [15, 11, 3, 1],
      .equation 350 true false
        []
        [11, 3, 1],
      .prior 4353 false [3, 1],
      .prior 5329 false [1]]⟩,
    ⟨[6601], [2121], [
      .prior 11511 true [],
      .prior 11512 true [13],
      .prior 11513 true [7, 13],
      .prior 11557 false [7, 13],
      .prior 5291 false [7, 13],
      .prior 10794 false [13],
      .prior 10789 false []]⟩,
    ⟨[2121, 5], [6599], [
      .prior 11558 true [5],
      .prior 11510 false []]⟩,
    ⟨[6615, 5], [625], [
      .prior 11552 false [],
      .prior 11556 false []]⟩,
    ⟨[1817, 15], [1817, 15], [
]⟩,
    ⟨[6615], [6615], [
]⟩,
    ⟨[1817, 15], [6615], [
      .prior 11561 false [],
      .prior 5326 true [15],
      .equation 350 false false
        []
        [5, 15],
      .prior 11560 true [15, 5, 15],
      .equation 30 false false
        [6615]
        [],
      .prior 11562 false []]⟩,
    ⟨[6615, 17], [6615, 17], [
]⟩,
    ⟨[6615, 17], [6615], [
      .prior 11564 false [],
      .prior 11555 true [17],
      .prior 1262 true [5, 17],
      .prior 11560 true [17, 5, 17],
      .equation 31 false false
        [6615]
        [],
      .prior 11562 false []]⟩,
    ⟨[6615, 13], [309], [
      .prior 11549 false [],
      .prior 11550 false []]⟩,
    ⟨[6615, 7], [6615, 7], [
]⟩,
    ⟨[6615, 7], [6615], [
      .prior 11567 false [],
      .prior 11551 true [7],
      .prior 905 true [13, 7],
      .prior 11566 true [7, 13, 7],
      .equation 22 false false
        [6615, 6]
        [7],
      .prior 11562 false []]⟩,
    ⟨[5573, 13], [5573, 13], [
]⟩,
    ⟨[6599], [6599], [
]⟩,
    ⟨[5573, 13], [6599], [
      .prior 11569 false [],
      .prior 10757 true [13],
      .equation 29 false false
        [5575]
        [12, 4],
      .equation 10 true false
        [5575, 12]
        [4],
      .prior 10789 false [4],
      .equation 6 true false
        [2121, 4]
        [],
      .prior 11559 false [],
      .prior 11570 false []]⟩,
    ⟨[6599, 13], [5573], [
      .prior 11571 true [13],
      .equation 10 false false
        [5573]
        []]⟩,
    ⟨[3681, 1], [6599], [
      .prior 8041 true [1],
      .equation 1098 false false
        []
        [5, 1],
      .equation 26 false false
        [2121]
        [4],
      .equation 6 true false
        [2121, 4]
        [],
      .prior 11559 false [],
      .prior 11570 false []]⟩,
    ⟨[6599, 1], [3681], [
      .prior 11573 true [1],
      .equation 2 false false
        [3681]
        []]⟩,
    ⟨[5573], [3685], [
      .equation 40 true false
        [5573, 0]
        [1],
      .prior 11569 false [1, 13, 1],
      .prior 11571 false [1, 13, 1],
      .prior 11574 false [13, 1],
      .equation 1878 true false
        []
        [1],
      .equation 1879 true false
        []
        []]⟩,
    ⟨[3685, 5], [5575], [
      .prior 11575 true [5],
      .equation 2824 true false
        []
        []]⟩,
    ⟨[3685, 13], [6599], [
      .prior 11575 true [13],
      .prior 11571 false []]⟩,
    ⟨[5573], [3685], [
      .prior 11575 false []]⟩,
    ⟨[6617, 11], [3679], [
      .equation 3345 false false
        []
        [11],
      .equation 8 false false
        [3679]
        []]⟩,
    ⟨[3679, 11], [6617], [
      .equation 3345 true false
        []
        []]⟩,
    ⟨[6617, 1], [6617, 1], [
]⟩,
    ⟨[6617, 1], [2559], [
      .prior 11581 false [],
      .prior 11580 true [1],
      .equation 43 false false
        [3679, 0]
        [10, 0, 10],
      .equation 2 true false
        [3679, 0]
        [10, 0, 10],
      .prior 7998 false [10, 0, 10],
      .equation 8 true false
        [2717, 10]
        [0, 10],
      .prior 6989 false [0, 10],
      .equation 2 true false
        [2123, 0]
        [10],
      .prior 5939 false [10],
      .equation 8 true false
        [2121, 10]
        [],
      .prior 9628 false [],
      .prior 6763 false []]⟩,
    ⟨[2559, 1], [6617], [
      .prior 11582 true [1],
      .equation 2 false false
        [6617]
        []]⟩,
    ⟨[6617, 3], [2275], [
      .prior 11580 true [3],
      .equation 34 false false
        [3679, 2]
        [10],
      .equation 4 true false
        [3679, 2]
        [10],
      .prior 7995 false [10],
      .equation 8 true false
        [2279, 10]
        [],
      .prior 6290 false [],
      .prior 6317 false [],
      .prior 6320 false []]⟩,
    ⟨[6617, 5], [2723], [
      .prior 11580 true [5],
      .equation 28 false false
        [3679, 4]
        [10],
      .prior 8008 false [10],
      .equation 8 true false
        [2721, 10]
        [],
      .equation 1398 true false
        []
        [],
      .prior 8017 false []]⟩,
    ⟨[2723, 5], [6617], [
      .prior 11585 true [5],
      .equation 6 false false
        [6617]
        []]⟩,
    ⟨[6617, 7], [1549], [
      .prior 11580 true [7],
      .equation 21 false false
        [3679, 6]
        [10],
      .equation 17 true false
        [3679, 6]
        [10],
      .prior 8007 false [10],
      .equation 8 true false
        [1551, 10]
        [],
      .prior 4537 false [],
      .prior 4535 false []]⟩,
    ⟨[1549, 7], [6617], [
      .prior 11587 true [7],
      .equation 17 false false
        [6617]
        []]⟩,
    ⟨[6617], [6617], [
]⟩,
    ⟨[6617, 15], [6617], [
      .prior 11580 true [15],
      .equation 136 false false
        [3679]
        [14, 10],
      .equation 12 true false
        [3679, 14]
        [10],
      .prior 8001 false [10],
      .equation 8 true false
        [3679, 10]
        [],
      .equation 3345 true false
        []
        [],
      .prior 11589 false []]⟩,
    ⟨[2563, 17], [6617], [
      .equation 1318 false false
        []
        [17],
      .equation 1317 false false
        []
        [1, 17],
      .prior 11582 true [17, 1, 17],
      .prior 11581 true [17, 1, 17],
      .equation 41 false false
        [6617]
        [],
      .prior 11589 false []]⟩,
    ⟨[6619, 7], [2725], [
      .equation 3346 false false
        []
        [7],
      .equation 17 false false
        [2725]
        []]⟩,
    ⟨[2725, 7], [6619], [
      .equation 3346 true false
        []
        []]⟩,
    ⟨[2725, 10, 6], [6619], [
      .equation 8 true false
        [2725, 10]
        [6],
      .prior 7007 true [11, 6],
      .equation 139 false false
        [2723, 10]
        [12, 10, 12, 6],
      .equation 8 true false
        [2723, 10]
        [12, 10, 12, 6],
      .prior 7005 false [12, 10, 12, 6],
      .equation 10 true false
        [2721, 12]
        [10, 12, 6],
      .prior 7004 false [10, 12, 6],
      .equation 8 true false
        [2721, 10]
        [12, 6],
      .equation 1398 true false
        []
        [12, 6],
      .equation 10 true false
        [2723, 12]
        [6],
      .equation 1399 true false
        []
        [6],
      .prior 7008 false [6],
      .equation 17 true false
        [2725, 6]
        [],
      .equation 3346 true false
        []
        []]⟩,
    ⟨[6619, 11], [6619, 11], [
]⟩,
    ⟨[6619], [6619], [
]⟩,
    ⟨[6619, 15], [6619, 15], [
]⟩,
    ⟨[6621, 1], [6619], [
      .equation 3347 false false
        []
        [1],
      .equation 2 false false
        [6619]
        []]⟩,
    ⟨[6619, 1], [6621], [
      .equation 3347 true false
        []
        []]⟩,
    ⟨[6621, 7], [2727], [
      .prior 11599 true [7],
      .equation 18 false false
        [6619]
        [6, 0],
      .equation 17 true false
        [6619, 6]
        [0],
      .prior 11592 false [0],
      .equation 2 true false
        [2725, 0]
        [],
      .equation 1400 true false
        []
        []]⟩,
    ⟨[2727, 7], [6621], [
      .prior 11600 true [7],
      .equation 17 false false
        [6621]
        []]⟩,
    ⟨[6623, 3], [6621], [
      .equation 3348 false false
        []
        [3],
      .equation 4 false false
        [6621]
        []]⟩,
    ⟨[6625, 11], [6623], [
      .equation 3349 false false
        []
        [11],
      .equation 8 false false
        [6623]
        []]⟩,
    ⟨[6637, 3], [6635], [
      .equation 3355 false false
        []
        [3],
      .equation 4 false false
        [6635]
        []]⟩,
    ⟨[6639, 11], [6637], [
      .equation 3356 false false
        []
        [11],
      .equation 8 false false
        [6637]
        []]⟩,
    ⟨[6641, 15], [6639], [
      .equation 3357 false false
        []
        [15],
      .equation 12 false false
        [6639]
        []]⟩,
    ⟨[6643, 5], [6641], [
      .equation 3358 false false
        []
        [5],
      .equation 6 false false
        [6641]
        []]⟩,
    ⟨[6645, 13], [6643], [
      .equation 3359 false false
        []
        [13],
      .equation 10 false false
        [6643]
        []]⟩,
    ⟨[6723, 3], [6721], [
      .equation 3398 false false
        []
        [3],
      .equation 4 false false
        [6721]
        []]⟩,
    ⟨[6727, 15], [6725], [
      .equation 3400 false false
        []
        [15],
      .equation 12 false false
        [6725]
        []]⟩,
    ⟨[6737, 3], [6735], [
      .equation 3405 false false
        []
        [3],
      .equation 4 false false
        [6735]
        []]⟩,
    ⟨[6739, 11], [6737], [
      .equation 3406 false false
        []
        [11],
      .equation 8 false false
        [6737]
        []]⟩,
    ⟨[6743, 5], [6741], [
      .equation 3408 false false
        []
        [5],
      .equation 6 false false
        [6741]
        []]⟩,
    ⟨[6745, 13], [6743], [
      .equation 3409 false false
        []
        [13],
      .equation 10 false false
        [6743]
        []]⟩,
    ⟨[6747, 7], [6745], [
      .equation 3410 false false
        []
        [7],
      .equation 17 false false
        [6745]
        []]⟩,
    ⟨[6749, 1], [6747], [
      .equation 3411 false false
        []
        [1],
      .equation 2 false false
        [6747]
        []]⟩,
    ⟨[6751, 3], [6749], [
      .equation 3412 false false
        []
        [3],
      .equation 4 false false
        [6749]
        []]⟩,
    ⟨[6753, 11], [6751], [
      .equation 3413 false false
        []
        [11],
      .equation 8 false false
        [6751]
        []]⟩,
    ⟨[6755, 15], [6753], [
      .equation 3414 false false
        []
        [15],
      .equation 12 false false
        [6753]
        []]⟩,
    ⟨[6757, 5], [6755], [
      .equation 3415 false false
        []
        [5],
      .equation 6 false false
        [6755]
        []]⟩,
    ⟨[6759, 13], [6757], [
      .equation 3416 false false
        []
        [13],
      .equation 10 false false
        [6757]
        []]⟩,
    ⟨[6761, 7], [6759], [
      .equation 3417 false false
        []
        [7],
      .equation 17 false false
        [6759]
        []]⟩,
    ⟨[6763, 1], [6761], [
      .equation 3418 false false
        []
        [1],
      .equation 2 false false
        [6761]
        []]⟩,
    ⟨[6765, 3], [6763], [
      .equation 3419 false false
        []
        [3],
      .equation 4 false false
        [6763]
        []]⟩,
    ⟨[6767, 11], [6765], [
      .equation 3420 false false
        []
        [11],
      .equation 8 false false
        [6765]
        []]⟩,
    ⟨[6769, 15], [6767], [
      .equation 3421 false false
        []
        [15],
      .equation 12 false false
        [6767]
        []]⟩,
    ⟨[6771, 5], [6769], [
      .equation 3422 false false
        []
        [5],
      .equation 6 false false
        [6769]
        []]⟩,
    ⟨[6773, 13], [6771], [
      .equation 3423 false false
        []
        [13],
      .equation 10 false false
        [6771]
        []]⟩,
    ⟨[6775, 7], [6773], [
      .equation 3424 false false
        []
        [7],
      .equation 17 false false
        [6773]
        []]⟩,
    ⟨[6777, 1], [6775], [
      .equation 3425 false false
        []
        [1],
      .equation 2 false false
        [6775]
        []]⟩,
    ⟨[6779, 3], [6777], [
      .equation 3426 false false
        []
        [3],
      .equation 4 false false
        [6777]
        []]⟩,
    ⟨[6781, 11], [6779], [
      .equation 3427 false false
        []
        [11],
      .equation 8 false false
        [6779]
        []]⟩,
    ⟨[6783, 15], [6781], [
      .equation 3428 false false
        []
        [15],
      .equation 12 false false
        [6781]
        []]⟩,
    ⟨[6785, 5], [6783], [
      .equation 3429 false false
        []
        [5],
      .equation 6 false false
        [6783]
        []]⟩,
    ⟨[6787, 13], [6785], [
      .equation 3430 false false
        []
        [13],
      .equation 10 false false
        [6785]
        []]⟩,
    ⟨[6789, 7], [6787], [
      .equation 3431 false false
        []
        [7],
      .equation 17 false false
        [6787]
        []]⟩,
    ⟨[6791, 1], [6789], [
      .equation 3432 false false
        []
        [1],
      .equation 2 false false
        [6789]
        []]⟩,
    ⟨[6793, 3], [6791], [
      .equation 3433 false false
        []
        [3],
      .equation 4 false false
        [6791]
        []]⟩,
    ⟨[6795, 11], [6793], [
      .equation 3434 false false
        []
        [11],
      .equation 8 false false
        [6793]
        []]⟩,
    ⟨[6797, 15], [6795], [
      .equation 3435 false false
        []
        [15],
      .equation 12 false false
        [6795]
        []]⟩,
    ⟨[6799, 5], [6797], [
      .equation 3436 false false
        []
        [5],
      .equation 6 false false
        [6797]
        []]⟩,
    ⟨[6801, 13], [6799], [
      .equation 3437 false false
        []
        [13],
      .equation 10 false false
        [6799]
        []]⟩,
    ⟨[6803, 7], [6801], [
      .equation 3438 false false
        []
        [7],
      .equation 17 false false
        [6801]
        []]⟩,
    ⟨[6805, 1], [6803], [
      .equation 3439 false false
        []
        [1],
      .equation 2 false false
        [6803]
        []]⟩,
    ⟨[6807, 3], [6805], [
      .equation 3440 false false
        []
        [3],
      .equation 4 false false
        [6805]
        []]⟩,
    ⟨[6809, 11], [6807], [
      .equation 3441 false false
        []
        [11],
      .equation 8 false false
        [6807]
        []]⟩,
    ⟨[6811, 15], [6809], [
      .equation 3442 false false
        []
        [15],
      .equation 12 false false
        [6809]
        []]⟩]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
