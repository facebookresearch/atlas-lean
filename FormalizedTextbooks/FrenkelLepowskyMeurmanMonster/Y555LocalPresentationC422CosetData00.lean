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
def y422CosetData00 : Fin 128 → Y522RawCosetCertificate :=
  ![
    ⟨[21, 9], [], [
      .equation 0 false false
        []
        [9],
      .equation 1 false false
        []
        []]⟩,
    ⟨[9], [21], [
      .equation 0 true false
        []
        []]⟩,
    ⟨[21, 1], [21, 1], [
]⟩,
    ⟨[21], [21], [
]⟩,
    ⟨[21, 1], [21], [
      .prior 2 false [],
      .prior 1 true [1],
      .equation 3 false false
        [0]
        [8],
      .equation 2 true false
        [0]
        [8],
      .fixed 0 false [8],
      .equation 1 true false
        [8]
        [],
      .equation 0 true false
        []
        [],
      .prior 3 false []]⟩,
    ⟨[21, 3], [21, 3], [
]⟩,
    ⟨[21, 3], [21], [
      .prior 5 false [],
      .prior 1 true [3],
      .equation 5 false false
        [2]
        [8],
      .equation 4 true false
        [2]
        [8],
      .fixed 1 false [8],
      .equation 1 true false
        [8]
        [],
      .equation 0 true false
        []
        [],
      .prior 3 false []]⟩,
    ⟨[21, 5], [21, 5], [
]⟩,
    ⟨[21, 5], [21], [
      .prior 7 false [],
      .prior 1 true [5],
      .equation 7 false false
        [4]
        [8],
      .equation 6 true false
        [4]
        [8],
      .fixed 2 false [8],
      .equation 1 true false
        [8]
        [],
      .equation 0 true false
        []
        [],
      .prior 3 false []]⟩,
    ⟨[21, 11], [21, 11], [
]⟩,
    ⟨[21, 11], [21], [
      .prior 9 false [],
      .prior 1 true [11],
      .equation 9 false false
        []
        [10, 8],
      .equation 8 true false
        [10]
        [8],
      .fixed 4 false [8],
      .equation 1 true false
        [8]
        [],
      .equation 0 true false
        []
        [],
      .prior 3 false []]⟩,
    ⟨[21, 13], [21, 13], [
]⟩,
    ⟨[21, 13], [21], [
      .prior 11 false [],
      .prior 1 true [13],
      .equation 11 false false
        []
        [12, 8],
      .equation 10 true false
        [12]
        [8],
      .fixed 5 false [8],
      .equation 1 true false
        [8]
        [],
      .equation 0 true false
        []
        [],
      .prior 3 false []]⟩,
    ⟨[21, 15], [21, 15], [
]⟩,
    ⟨[21, 15], [21], [
      .prior 13 false [],
      .prior 1 true [15],
      .equation 13 false false
        []
        [14, 8],
      .equation 12 true false
        [14]
        [8],
      .fixed 6 false [8],
      .equation 1 true false
        [8]
        [],
      .equation 0 true false
        []
        [],
      .prior 3 false []]⟩,
    ⟨[21, 17], [21, 17], [
]⟩,
    ⟨[21, 17], [21], [
      .prior 15 false [],
      .prior 1 true [17],
      .equation 15 false false
        []
        [16, 8],
      .equation 14 true false
        [16]
        [8],
      .fixed 7 false [8],
      .equation 1 true false
        [8]
        [],
      .equation 0 true false
        []
        [],
      .prior 3 false []]⟩,
    ⟨[23, 7], [21], [
      .equation 16 false false
        []
        [7],
      .equation 17 false false
        [21]
        []]⟩,
    ⟨[21, 7], [23], [
      .equation 16 true false
        []
        []]⟩,
    ⟨[23, 1], [23, 1], [
]⟩,
    ⟨[23], [23], [
]⟩,
    ⟨[23, 1], [23], [
      .prior 19 false [],
      .prior 18 true [1],
      .equation 18 false false
        [21, 0]
        [6],
      .equation 2 true false
        [21, 0]
        [6],
      .prior 4 false [6],
      .equation 17 true false
        [21, 6]
        [],
      .equation 16 true false
        []
        [],
      .prior 20 false []]⟩,
    ⟨[23, 3], [23, 3], [
]⟩,
    ⟨[23, 3], [23], [
      .prior 22 false [],
      .prior 18 true [3],
      .equation 19 false false
        [21, 2]
        [6],
      .equation 4 true false
        [21, 2]
        [6],
      .prior 6 false [6],
      .equation 17 true false
        [21, 6]
        [],
      .equation 16 true false
        []
        [],
      .prior 20 false []]⟩,
    ⟨[23, 9], [23, 9], [
]⟩,
    ⟨[23, 9], [23], [
      .prior 24 false [],
      .prior 18 true [9],
      .equation 20 false false
        [21]
        [8, 6, 8, 6],
      .equation 1 true false
        [21, 8]
        [6, 8, 6],
      .prior 0 false [6, 8, 6],
      .equation 17 true false
        [6]
        [8, 6],
      .fixed 3 false [8, 6],
      .equation 1 true false
        [8]
        [6],
      .equation 0 true false
        []
        [6],
      .equation 17 true false
        [21, 6]
        [],
      .equation 16 true false
        []
        [],
      .prior 20 false []]⟩,
    ⟨[23, 11], [23, 11], [
]⟩,
    ⟨[23, 11], [23], [
      .prior 26 false [],
      .prior 18 true [11],
      .equation 21 false false
        [21]
        [10, 6],
      .equation 8 true false
        [21, 10]
        [6],
      .prior 10 false [6],
      .equation 17 true false
        [21, 6]
        [],
      .equation 16 true false
        []
        [],
      .prior 20 false []]⟩,
    ⟨[23, 13], [23, 13], [
]⟩,
    ⟨[23, 13], [23], [
      .prior 28 false [],
      .prior 18 true [13],
      .equation 22 false false
        [21]
        [12, 6],
      .equation 10 true false
        [21, 12]
        [6],
      .prior 12 false [6],
      .equation 17 true false
        [21, 6]
        [],
      .equation 16 true false
        []
        [],
      .prior 20 false []]⟩,
    ⟨[23, 15], [23, 15], [
]⟩,
    ⟨[23, 15], [23], [
      .prior 30 false [],
      .prior 18 true [15],
      .equation 23 false false
        [21]
        [14, 6],
      .equation 12 true false
        [21, 14]
        [6],
      .prior 14 false [6],
      .equation 17 true false
        [21, 6]
        [],
      .equation 16 true false
        []
        [],
      .prior 20 false []]⟩,
    ⟨[23, 17], [23, 17], [
]⟩,
    ⟨[23, 17], [23], [
      .prior 32 false [],
      .prior 18 true [17],
      .equation 24 false false
        [21]
        [16, 6],
      .equation 14 true false
        [21, 16]
        [6],
      .prior 16 false [6],
      .equation 17 true false
        [21, 6]
        [],
      .equation 16 true false
        []
        [],
      .prior 20 false []]⟩,
    ⟨[25, 5], [23], [
      .equation 25 false false
        []
        [5],
      .equation 6 false false
        [23]
        []]⟩,
    ⟨[23, 5], [25], [
      .equation 25 true false
        []
        []]⟩,
    ⟨[25, 1], [25, 1], [
]⟩,
    ⟨[25], [25], [
]⟩,
    ⟨[25, 1], [25], [
      .prior 36 false [],
      .prior 35 true [1],
      .equation 26 false false
        [23, 0]
        [4],
      .equation 2 true false
        [23, 0]
        [4],
      .prior 21 false [4],
      .equation 6 true false
        [23, 4]
        [],
      .equation 25 true false
        []
        [],
      .prior 37 false []]⟩,
    ⟨[25, 7], [25, 7], [
]⟩,
    ⟨[25, 7], [25], [
      .prior 39 false [],
      .prior 35 true [7],
      .equation 27 false false
        [23]
        [6, 4, 6, 4],
      .equation 17 true false
        [23, 6]
        [4, 6, 4],
      .prior 17 false [4, 6, 4],
      .equation 6 true false
        [21, 4]
        [6, 4],
      .prior 8 false [6, 4],
      .equation 17 true false
        [21, 6]
        [4],
      .equation 16 true false
        []
        [4],
      .equation 6 true false
        [23, 4]
        [],
      .equation 25 true false
        []
        [],
      .prior 37 false []]⟩,
    ⟨[25, 9], [25, 9], [
]⟩,
    ⟨[25, 9], [25], [
      .prior 41 false [],
      .prior 35 true [9],
      .equation 7 false false
        [23]
        [8, 4],
      .equation 1 true false
        [23, 8]
        [4],
      .prior 25 false [4],
      .equation 6 true false
        [23, 4]
        [],
      .equation 25 true false
        []
        [],
      .prior 37 false []]⟩,
    ⟨[25, 11], [25, 11], [
]⟩,
    ⟨[25, 11], [25], [
      .prior 43 false [],
      .prior 35 true [11],
      .equation 28 false false
        [23]
        [10, 4],
      .equation 8 true false
        [23, 10]
        [4],
      .prior 27 false [4],
      .equation 6 true false
        [23, 4]
        [],
      .equation 25 true false
        []
        [],
      .prior 37 false []]⟩,
    ⟨[25, 13], [25, 13], [
]⟩,
    ⟨[25, 13], [25], [
      .prior 45 false [],
      .prior 35 true [13],
      .equation 29 false false
        [23]
        [12, 4],
      .equation 10 true false
        [23, 12]
        [4],
      .prior 29 false [4],
      .equation 6 true false
        [23, 4]
        [],
      .equation 25 true false
        []
        [],
      .prior 37 false []]⟩,
    ⟨[25, 15], [25, 15], [
]⟩,
    ⟨[25, 15], [25], [
      .prior 47 false [],
      .prior 35 true [15],
      .equation 30 false false
        [23]
        [14, 4],
      .equation 12 true false
        [23, 14]
        [4],
      .prior 31 false [4],
      .equation 6 true false
        [23, 4]
        [],
      .equation 25 true false
        []
        [],
      .prior 37 false []]⟩,
    ⟨[25, 17], [25, 17], [
]⟩,
    ⟨[25, 17], [25], [
      .prior 49 false [],
      .prior 35 true [17],
      .equation 31 false false
        [23]
        [16, 4],
      .equation 14 true false
        [23, 16]
        [4],
      .prior 33 false [4],
      .equation 6 true false
        [23, 4]
        [],
      .equation 25 true false
        []
        [],
      .prior 37 false []]⟩,
    ⟨[27, 3], [25], [
      .equation 32 false false
        []
        [3],
      .equation 4 false false
        [25]
        []]⟩,
    ⟨[25, 3], [27], [
      .equation 32 true false
        []
        []]⟩,
    ⟨[27, 5], [27, 5], [
]⟩,
    ⟨[27], [27], [
]⟩,
    ⟨[27, 5], [27], [
      .prior 53 false [],
      .prior 52 true [5],
      .equation 33 false false
        [25]
        [4, 2, 4, 2],
      .equation 6 true false
        [25, 4]
        [2, 4, 2],
      .prior 34 false [2, 4, 2],
      .equation 4 true false
        [23, 2]
        [4, 2],
      .prior 23 false [4, 2],
      .equation 6 true false
        [23, 4]
        [2],
      .equation 25 true false
        []
        [2],
      .equation 4 true false
        [25, 2]
        [],
      .equation 32 true false
        []
        [],
      .prior 54 false []]⟩,
    ⟨[27, 7], [27, 7], [
]⟩,
    ⟨[27, 7], [27], [
      .prior 56 false [],
      .prior 52 true [7],
      .equation 19 false false
        [25]
        [6, 2],
      .equation 17 true false
        [25, 6]
        [2],
      .prior 40 false [2],
      .equation 4 true false
        [25, 2]
        [],
      .equation 32 true false
        []
        [],
      .prior 54 false []]⟩,
    ⟨[27, 9], [27, 9], [
]⟩,
    ⟨[27, 9], [27], [
      .prior 58 false [],
      .prior 52 true [9],
      .equation 5 false false
        [25]
        [8, 2],
      .equation 1 true false
        [25, 8]
        [2],
      .prior 42 false [2],
      .equation 4 true false
        [25, 2]
        [],
      .equation 32 true false
        []
        [],
      .prior 54 false []]⟩,
    ⟨[27, 11], [27, 11], [
]⟩,
    ⟨[27, 11], [27], [
      .prior 60 false [],
      .prior 52 true [11],
      .equation 34 false false
        [25]
        [10, 2],
      .equation 8 true false
        [25, 10]
        [2],
      .prior 44 false [2],
      .equation 4 true false
        [25, 2]
        [],
      .equation 32 true false
        []
        [],
      .prior 54 false []]⟩,
    ⟨[27, 13], [27, 13], [
]⟩,
    ⟨[27, 13], [27], [
      .prior 62 false [],
      .prior 52 true [13],
      .equation 35 false false
        [25]
        [12, 2],
      .equation 10 true false
        [25, 12]
        [2],
      .prior 46 false [2],
      .equation 4 true false
        [25, 2]
        [],
      .equation 32 true false
        []
        [],
      .prior 54 false []]⟩,
    ⟨[27, 15], [27, 15], [
]⟩,
    ⟨[27, 15], [27], [
      .prior 64 false [],
      .prior 52 true [15],
      .equation 36 false false
        [25]
        [14, 2],
      .equation 12 true false
        [25, 14]
        [2],
      .prior 48 false [2],
      .equation 4 true false
        [25, 2]
        [],
      .equation 32 true false
        []
        [],
      .prior 54 false []]⟩,
    ⟨[27, 17], [27, 17], [
]⟩,
    ⟨[27, 17], [27], [
      .prior 66 false [],
      .prior 52 true [17],
      .equation 37 false false
        [25]
        [16, 2],
      .equation 14 true false
        [25, 16]
        [2],
      .prior 50 false [2],
      .equation 4 true false
        [25, 2]
        [],
      .equation 32 true false
        []
        [],
      .prior 54 false []]⟩,
    ⟨[29, 1], [27], [
      .equation 38 false false
        []
        [1],
      .equation 2 false false
        [27]
        []]⟩,
    ⟨[27, 1], [29], [
      .equation 38 true false
        []
        []]⟩,
    ⟨[29, 3], [29, 3], [
]⟩,
    ⟨[29], [29], [
]⟩,
    ⟨[29, 3], [29], [
      .prior 70 false [],
      .prior 69 true [3],
      .equation 39 false false
        [27]
        [2, 0, 2, 0],
      .equation 4 true false
        [27, 2]
        [0, 2, 0],
      .prior 51 false [0, 2, 0],
      .equation 2 true false
        [25, 0]
        [2, 0],
      .prior 38 false [2, 0],
      .equation 4 true false
        [25, 2]
        [0],
      .equation 32 true false
        []
        [0],
      .equation 2 true false
        [27, 0]
        [],
      .equation 38 true false
        []
        [],
      .prior 71 false []]⟩,
    ⟨[29, 5], [29, 5], [
]⟩,
    ⟨[29, 5], [29], [
      .prior 73 false [],
      .prior 69 true [5],
      .equation 26 false false
        [27]
        [4, 0],
      .equation 6 true false
        [27, 4]
        [0],
      .prior 55 false [0],
      .equation 2 true false
        [27, 0]
        [],
      .equation 38 true false
        []
        [],
      .prior 71 false []]⟩,
    ⟨[29, 7], [29, 7], [
]⟩,
    ⟨[29, 7], [29], [
      .prior 75 false [],
      .prior 69 true [7],
      .equation 18 false false
        [27]
        [6, 0],
      .equation 17 true false
        [27, 6]
        [0],
      .prior 57 false [0],
      .equation 2 true false
        [27, 0]
        [],
      .equation 38 true false
        []
        [],
      .prior 71 false []]⟩,
    ⟨[29, 9], [29, 9], [
]⟩,
    ⟨[29, 9], [29], [
      .prior 77 false [],
      .prior 69 true [9],
      .equation 3 false false
        [27]
        [8, 0],
      .equation 1 true false
        [27, 8]
        [0],
      .prior 59 false [0],
      .equation 2 true false
        [27, 0]
        [],
      .equation 38 true false
        []
        [],
      .prior 71 false []]⟩,
    ⟨[29, 13], [29, 13], [
]⟩,
    ⟨[29, 13], [29], [
      .prior 79 false [],
      .prior 69 true [13],
      .equation 40 false false
        [27]
        [12, 0],
      .equation 10 true false
        [27, 12]
        [0],
      .prior 63 false [0],
      .equation 2 true false
        [27, 0]
        [],
      .equation 38 true false
        []
        [],
      .prior 71 false []]⟩,
    ⟨[29, 17], [29, 17], [
]⟩,
    ⟨[29, 17], [29], [
      .prior 81 false [],
      .prior 69 true [17],
      .equation 41 false false
        [27]
        [16, 0],
      .equation 14 true false
        [27, 16]
        [0],
      .prior 67 false [0],
      .equation 2 true false
        [27, 0]
        [],
      .equation 38 true false
        []
        [],
      .prior 71 false []]⟩,
    ⟨[31, 11], [29], [
      .equation 42 false false
        []
        [11],
      .equation 8 false false
        [29]
        []]⟩,
    ⟨[29, 11], [31], [
      .equation 42 true false
        []
        []]⟩,
    ⟨[31, 1], [31, 1], [
]⟩,
    ⟨[31], [31], [
]⟩,
    ⟨[31, 1], [31], [
      .prior 85 false [],
      .prior 84 true [1],
      .equation 43 false false
        [29, 0]
        [10, 0, 10],
      .equation 2 true false
        [29, 0]
        [10, 0, 10],
      .prior 68 false [10, 0, 10],
      .equation 8 true false
        [27, 10]
        [0, 10],
      .prior 61 false [0, 10],
      .equation 2 true false
        [27, 0]
        [10],
      .equation 38 true false
        []
        [10],
      .equation 8 true false
        [29, 10]
        [],
      .equation 42 true false
        []
        [],
      .prior 86 false []]⟩,
    ⟨[31, 3], [31, 3], [
]⟩,
    ⟨[31, 3], [31], [
      .prior 88 false [],
      .prior 84 true [3],
      .equation 34 false false
        [29, 2]
        [10],
      .equation 4 true false
        [29, 2]
        [10],
      .prior 72 false [10],
      .equation 8 true false
        [29, 10]
        [],
      .equation 42 true false
        []
        [],
      .prior 86 false []]⟩,
    ⟨[31, 5], [31, 5], [
]⟩,
    ⟨[31, 5], [31], [
      .prior 90 false [],
      .prior 84 true [5],
      .equation 28 false false
        [29, 4]
        [10],
      .equation 6 true false
        [29, 4]
        [10],
      .prior 74 false [10],
      .equation 8 true false
        [29, 10]
        [],
      .equation 42 true false
        []
        [],
      .prior 86 false []]⟩,
    ⟨[31, 7], [31, 7], [
]⟩,
    ⟨[31, 7], [31], [
      .prior 92 false [],
      .prior 84 true [7],
      .equation 21 false false
        [29, 6]
        [10],
      .equation 17 true false
        [29, 6]
        [10],
      .prior 76 false [10],
      .equation 8 true false
        [29, 10]
        [],
      .equation 42 true false
        []
        [],
      .prior 86 false []]⟩,
    ⟨[31, 9], [31, 9], [
]⟩,
    ⟨[31, 9], [31], [
      .prior 94 false [],
      .prior 84 true [9],
      .equation 9 false false
        [29, 8]
        [10],
      .equation 1 true false
        [29, 8]
        [10],
      .prior 78 false [10],
      .equation 8 true false
        [29, 10]
        [],
      .equation 42 true false
        []
        [],
      .prior 86 false []]⟩,
    ⟨[31, 17], [31, 17], [
]⟩,
    ⟨[31, 17], [31], [
      .prior 96 false [],
      .prior 84 true [17],
      .equation 44 false false
        [29]
        [16, 10],
      .equation 14 true false
        [29, 16]
        [10],
      .prior 82 false [10],
      .equation 8 true false
        [29, 10]
        [],
      .equation 42 true false
        []
        [],
      .prior 86 false []]⟩,
    ⟨[33, 15], [31], [
      .equation 45 false false
        []
        [15],
      .equation 12 false false
        [31]
        []]⟩,
    ⟨[31, 15], [33], [
      .equation 45 true false
        []
        []]⟩,
    ⟨[31, 2], [31], [
      .equation 4 true false
        [31, 2]
        [],
      .prior 89 false []]⟩,
    ⟨[33, 3], [33, 3], [
]⟩,
    ⟨[33], [33], [
]⟩,
    ⟨[33, 3], [33], [
      .prior 101 false [],
      .prior 99 true [3],
      .equation 36 false false
        [31, 2]
        [14],
      .prior 100 false [14],
      .equation 12 true false
        [31, 14]
        [],
      .equation 45 true false
        []
        [],
      .prior 102 false []]⟩,
    ⟨[31, 4], [31], [
      .equation 6 true false
        [31, 4]
        [],
      .prior 91 false []]⟩,
    ⟨[33, 5], [33, 5], [
]⟩,
    ⟨[33, 5], [33], [
      .prior 105 false [],
      .prior 99 true [5],
      .equation 30 false false
        [31, 4]
        [14],
      .prior 104 false [14],
      .equation 12 true false
        [31, 14]
        [],
      .equation 45 true false
        []
        [],
      .prior 102 false []]⟩,
    ⟨[31, 6], [31], [
      .equation 17 true false
        [31, 6]
        [],
      .prior 93 false []]⟩,
    ⟨[33, 7], [33, 7], [
]⟩,
    ⟨[33, 7], [33], [
      .prior 108 false [],
      .prior 99 true [7],
      .equation 23 false false
        [31, 6]
        [14],
      .prior 107 false [14],
      .equation 12 true false
        [31, 14]
        [],
      .equation 45 true false
        []
        [],
      .prior 102 false []]⟩,
    ⟨[31, 8], [31], [
      .equation 1 true false
        [31, 8]
        [],
      .prior 95 false []]⟩,
    ⟨[33, 9], [33, 9], [
]⟩,
    ⟨[33, 9], [33], [
      .prior 111 false [],
      .prior 99 true [9],
      .equation 13 false false
        [31, 8]
        [14],
      .prior 110 false [14],
      .equation 12 true false
        [31, 14]
        [],
      .equation 45 true false
        []
        [],
      .prior 102 false []]⟩,
    ⟨[35, 13], [33], [
      .equation 46 false false
        []
        [13],
      .equation 10 false false
        [33]
        []]⟩,
    ⟨[33, 13], [35], [
      .equation 46 true false
        []
        []]⟩,
    ⟨[35, 3], [35, 3], [
]⟩,
    ⟨[35], [35], [
]⟩,
    ⟨[35, 3], [35], [
      .prior 115 false [],
      .prior 114 true [3],
      .equation 35 false false
        [33, 2]
        [12],
      .equation 4 true false
        [33, 2]
        [12],
      .prior 103 false [12],
      .equation 10 true false
        [33, 12]
        [],
      .equation 46 true false
        []
        [],
      .prior 116 false []]⟩,
    ⟨[35, 5], [35, 5], [
]⟩,
    ⟨[35, 5], [35], [
      .prior 118 false [],
      .prior 114 true [5],
      .equation 29 false false
        [33, 4]
        [12],
      .equation 6 true false
        [33, 4]
        [12],
      .prior 106 false [12],
      .equation 10 true false
        [33, 12]
        [],
      .equation 46 true false
        []
        [],
      .prior 116 false []]⟩,
    ⟨[35, 7], [35, 7], [
]⟩,
    ⟨[35, 7], [35], [
      .prior 120 false [],
      .prior 114 true [7],
      .equation 22 false false
        [33, 6]
        [12],
      .equation 17 true false
        [33, 6]
        [12],
      .prior 109 false [12],
      .equation 10 true false
        [33, 12]
        [],
      .equation 46 true false
        []
        [],
      .prior 116 false []]⟩,
    ⟨[35, 9], [35, 9], [
]⟩,
    ⟨[35, 9], [35], [
      .prior 122 false [],
      .prior 114 true [9],
      .equation 11 false false
        [33, 8]
        [12],
      .equation 1 true false
        [33, 8]
        [12],
      .prior 112 false [12],
      .equation 10 true false
        [33, 12]
        [],
      .equation 46 true false
        []
        [],
      .prior 116 false []]⟩,
    ⟨[37, 1], [35], [
      .equation 47 false false
        []
        [1],
      .equation 2 false false
        [35]
        []]⟩,
    ⟨[35, 1], [37], [
      .equation 47 true false
        []
        []]⟩,
    ⟨[35, 4], [35], [
      .equation 6 true false
        [35, 4]
        [],
      .prior 119 false []]⟩,
    ⟨[37, 5], [37, 5], [
]⟩]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
