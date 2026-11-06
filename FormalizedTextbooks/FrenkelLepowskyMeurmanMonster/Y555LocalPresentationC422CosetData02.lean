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
def y422CosetData02 : Fin 128 → Y522RawCosetCertificate :=
  ![
    ⟨[
      209, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 8, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0
    ], [], [
      .prior 255 false [12, 4, 14, 10, 2, 0],
      .equation 10 true false
        [12]
        [4, 14, 10, 2, 0],
      .fixed 5 false [4, 14, 10, 2, 0],
      .equation 6 true false
        [4]
        [14, 10, 2, 0],
      .fixed 2 false [14, 10, 2, 0],
      .equation 12 true false
        [14]
        [10, 2, 0],
      .fixed 6 false [10, 2, 0],
      .equation 8 true false
        [10]
        [2, 0],
      .fixed 4 false [2, 0],
      .equation 4 true false
        [2]
        [0],
      .fixed 1 false [0],
      .equation 2 true false
        [0]
        [],
      .fixed 0 false []]⟩,
    ⟨[
      209, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 8, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0
    ], [0], [
      .prior 256 false [
        6, 12, 4, 14, 10, 2, 0
      ],
      .equation 17 true false
        [6]
        [12, 4, 14, 10, 2, 0],
      .fixed 3 false [12, 4, 14, 10, 2, 0],
      .equation 10 true false
        [12]
        [4, 14, 10, 2, 0],
      .fixed 5 false [4, 14, 10, 2, 0],
      .equation 6 true false
        [4]
        [14, 10, 2, 0],
      .fixed 2 false [14, 10, 2, 0],
      .equation 12 true false
        [14]
        [10, 2, 0],
      .fixed 6 false [10, 2, 0],
      .equation 8 true false
        [10]
        [2, 0],
      .fixed 4 false [2, 0],
      .equation 4 true false
        [2]
        [0],
      .fixed 1 false [0]]⟩,
    ⟨[
      209, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 8, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2
    ], [3], [
      .prior 257 false [6, 12, 4, 14, 10, 2],
      .equation 2 true false
        [0]
        [6, 12, 4, 14, 10, 2],
      .fixed 0 false [6, 12, 4, 14, 10, 2],
      .equation 17 true false
        [6]
        [12, 4, 14, 10, 2],
      .fixed 3 false [12, 4, 14, 10, 2],
      .equation 10 true false
        [12]
        [4, 14, 10, 2],
      .fixed 5 false [4, 14, 10, 2],
      .equation 6 true false
        [4]
        [14, 10, 2],
      .fixed 2 false [14, 10, 2],
      .equation 12 true false
        [14]
        [10, 2],
      .fixed 6 false [10, 2],
      .equation 8 true false
        [10]
        [2],
      .fixed 4 false [2],
      .equation 4 true false
        [2]
        []]⟩,
    ⟨[
      209, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 8, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10
    ], [], [
      .prior 258 false [0, 6, 12, 4, 14, 10],
      .fixed 1 false [0, 6, 12, 4, 14, 10],
      .equation 2 true false
        [0]
        [6, 12, 4, 14, 10],
      .fixed 0 false [6, 12, 4, 14, 10],
      .equation 17 true false
        [6]
        [12, 4, 14, 10],
      .fixed 3 false [12, 4, 14, 10],
      .equation 10 true false
        [12]
        [4, 14, 10],
      .fixed 5 false [4, 14, 10],
      .equation 6 true false
        [4]
        [14, 10],
      .fixed 2 false [14, 10],
      .equation 12 true false
        [14]
        [10],
      .fixed 6 false [10],
      .equation 8 true false
        [10]
        [],
      .fixed 4 false []]⟩,
    ⟨[
      209, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 8, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14
    ], [], [
      .prior 259 false [2, 0, 6, 12, 4, 14],
      .equation 4 true false
        [2]
        [0, 6, 12, 4, 14],
      .fixed 1 false [0, 6, 12, 4, 14],
      .equation 2 true false
        [0]
        [6, 12, 4, 14],
      .fixed 0 false [6, 12, 4, 14],
      .equation 17 true false
        [6]
        [12, 4, 14],
      .fixed 3 false [12, 4, 14],
      .equation 10 true false
        [12]
        [4, 14],
      .fixed 5 false [4, 14],
      .equation 6 true false
        [4]
        [14],
      .fixed 2 false [14],
      .equation 12 true false
        [14]
        [],
      .fixed 6 false []]⟩,
    ⟨[
      209, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 8, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14
    ], [14], [
      .prior 260 false [
        10, 2, 0, 6, 12, 4, 14
      ],
      .equation 8 true false
        [10]
        [2, 0, 6, 12, 4, 14],
      .fixed 4 false [2, 0, 6, 12, 4, 14],
      .equation 4 true false
        [2]
        [0, 6, 12, 4, 14],
      .fixed 1 false [0, 6, 12, 4, 14],
      .equation 2 true false
        [0]
        [6, 12, 4, 14],
      .fixed 0 false [6, 12, 4, 14],
      .equation 17 true false
        [6]
        [12, 4, 14],
      .fixed 3 false [12, 4, 14],
      .equation 10 true false
        [12]
        [4, 14],
      .fixed 5 false [4, 14],
      .equation 6 true false
        [4]
        [14],
      .fixed 2 false [14]]⟩,
    ⟨[
      209, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 8, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4
    ], [5], [
      .prior 261 false [10, 2, 0, 6, 12, 4],
      .equation 12 true false
        [14]
        [10, 2, 0, 6, 12, 4],
      .fixed 6 false [10, 2, 0, 6, 12, 4],
      .equation 8 true false
        [10]
        [2, 0, 6, 12, 4],
      .fixed 4 false [2, 0, 6, 12, 4],
      .equation 4 true false
        [2]
        [0, 6, 12, 4],
      .fixed 1 false [0, 6, 12, 4],
      .equation 2 true false
        [0]
        [6, 12, 4],
      .fixed 0 false [6, 12, 4],
      .equation 17 true false
        [6]
        [12, 4],
      .fixed 3 false [12, 4],
      .equation 10 true false
        [12]
        [4],
      .fixed 5 false [4],
      .equation 6 true false
        [4]
        []]⟩,
    ⟨[
      209, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 8, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      8, 6
    ], [23], [
      .prior 262 false [14, 10, 2, 0, 8, 6],
      .fixed 2 false [14, 10, 2, 0, 8, 6],
      .equation 12 true false
        [14]
        [10, 2, 0, 8, 6],
      .fixed 6 false [10, 2, 0, 8, 6],
      .equation 8 true false
        [10]
        [2, 0, 8, 6],
      .fixed 4 false [2, 0, 8, 6],
      .equation 4 true false
        [2]
        [0, 8, 6],
      .fixed 1 false [0, 8, 6],
      .equation 2 true false
        [0]
        [8, 6],
      .fixed 0 false [8, 6],
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
        []]⟩,
    ⟨[
      209, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 8, 6, 12, 4, 14, 10, 2, 0,
      6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
      2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 8, 6, 12, 4,
      14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6,
      12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2,
      0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14,
      10, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
      4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
      8, 6, 12, 4, 14, 10, 2, 0
    ], [29], [
      .prior 263 false [12, 4, 14, 10, 2, 0],
      .equation 10 true false
        [23, 12]
        [4, 14, 10, 2, 0],
      .prior 29 false [4, 14, 10, 2, 0],
      .equation 6 true false
        [23, 4]
        [14, 10, 2, 0],
      .equation 25 true false
        []
        [14, 10, 2, 0],
      .equation 12 true false
        [25, 14]
        [10, 2, 0],
      .prior 48 false [10, 2, 0],
      .equation 8 true false
        [25, 10]
        [2, 0],
      .prior 44 false [2, 0],
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
        []]⟩,
    ⟨[211, 15], [211, 15], [
]⟩,
    ⟨[211, 15], [29], [
      .prior 265 false [],
      .equation 134 false false
        []
        [15],
      .equation 135 false false
        [
          209, 2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12,
          4, 14, 10, 2, 0, 6, 12, 4, 14, 10, 2, 0,
          6, 12, 4, 14, 10, 2, 0, 6, 12, 4, 14, 10,
          2, 0, 6, 12, 4, 14, 10, 2, 0, 6, 12, 4,
          14, 10, 2, 0
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
          14, 10, 2, 0, 6, 12, 4
        ],
      .prior 264 false [6, 12, 4],
      .equation 17 true false
        [29, 6]
        [12, 4],
      .prior 76 false [12, 4],
      .equation 10 true false
        [29, 12]
        [4],
      .prior 80 false [4],
      .equation 6 true false
        [29, 4]
        [],
      .prior 74 false [],
      .prior 71 false []]⟩,
    ⟨[29, 15], [211], [
      .prior 266 true [15],
      .equation 12 false false
        [211]
        []]⟩,
    ⟨[211, 11], [209], [
      .prior 234 false []]⟩,
    ⟨[211, 14], [29], [
      .equation 12 true false
        [211, 14]
        [],
      .prior 266 false []]⟩,
    ⟨[209], [33], [
      .equation 12 true false
        [209]
        [],
      .prior 268 true [15, 15],
      .equation 136 false false
        [211]
        [14, 10, 15],
      .prior 269 false [10, 15],
      .equation 8 true false
        [29, 10]
        [15],
      .equation 42 true false
        []
        [15],
      .prior 86 false [15],
      .prior 99 false []]⟩,
    ⟨[33, 11], [211], [
      .prior 270 true [11],
      .equation 134 true false
        []
        []]⟩,
    ⟨[209], [33], [
      .prior 270 false []]⟩,
    ⟨[33, 1], [205], [
      .prior 103 true [1],
      .prior 272 true [3, 1],
      .prior 233 false [1],
      .prior 232 false []]⟩,
    ⟨[211, 15], [29], [
      .prior 265 false [],
      .prior 266 false []]⟩,
    ⟨[211, 1], [211, 1], [
]⟩,
    ⟨[211], [211], [
]⟩,
    ⟨[211, 1], [211], [
      .prior 275 false [],
      .prior 267 true [1],
      .equation 38 false false
        []
        [15, 1],
      .prior 65 true [1, 15, 1],
      .prior 68 true [15, 1, 15, 1],
      .prior 274 true [1, 15, 1, 15, 1],
      .equation 137 false false
        [211, 0]
        [1],
      .prior 276 false []]⟩,
    ⟨[211, 3], [211, 3], [
]⟩,
    ⟨[211, 3], [211], [
      .prior 278 false [],
      .prior 267 true [3],
      .prior 72 true [15, 3],
      .prior 274 true [3, 15, 3],
      .equation 36 false false
        [211, 2]
        [3],
      .prior 276 false []]⟩,
    ⟨[211, 5], [211, 5], [
]⟩,
    ⟨[211, 5], [211], [
      .prior 280 false [],
      .prior 267 true [5],
      .prior 74 true [15, 5],
      .prior 274 true [5, 15, 5],
      .equation 30 false false
        [211, 4]
        [5],
      .prior 276 false []]⟩,
    ⟨[211, 7], [211, 7], [
]⟩,
    ⟨[211, 7], [211], [
      .prior 282 false [],
      .prior 267 true [7],
      .prior 76 true [15, 7],
      .prior 274 true [7, 15, 7],
      .equation 23 false false
        [211, 6]
        [7],
      .prior 276 false []]⟩,
    ⟨[211, 9], [211, 9], [
]⟩,
    ⟨[211, 9], [211], [
      .prior 284 false [],
      .prior 267 true [9],
      .prior 78 true [15, 9],
      .prior 274 true [9, 15, 9],
      .equation 13 false false
        [211, 8]
        [9],
      .prior 276 false []]⟩,
    ⟨[211, 13], [211, 13], [
]⟩,
    ⟨[211, 13], [211], [
      .prior 286 false [],
      .prior 267 true [13],
      .prior 80 true [15, 13],
      .prior 274 true [13, 15, 13],
      .equation 138 false false
        [211, 12]
        [13],
      .prior 276 false []]⟩,
    ⟨[33, 15], [31], [
      .prior 98 false []]⟩,
    ⟨[33, 0], [205], [
      .equation 2 true false
        [33, 0]
        [],
      .prior 273 false []]⟩,
    ⟨[33, 0], [205], [
      .prior 289 false []]⟩,
    ⟨[205], [205], [
]⟩,
    ⟨[33, 5], [33], [
      .prior 105 false [],
      .prior 106 false []]⟩,
    ⟨[33, 7], [33], [
      .prior 108 false [],
      .prior 109 false []]⟩,
    ⟨[203, 1], [203, 1], [
]⟩,
    ⟨[203, 1], [33], [
      .prior 294 false [],
      .prior 231 true [1],
      .prior 273 true [7, 1],
      .prior 293 true [1, 7, 1],
      .equation 18 false false
        [33, 0]
        [1],
      .prior 102 false []]⟩,
    ⟨[33, 1], [205], [
      .prior 273 false []]⟩,
    ⟨[205], [203], [
      .prior 296 true [],
      .prior 295 true [1],
      .equation 2 false false
        [203]
        []]⟩,
    ⟨[205], [203], [
      .prior 297 false []]⟩,
    ⟨[203, 15], [203], [
      .prior 297 true [15],
      .prior 273 true [15],
      .equation 45 false false
        []
        [1, 15],
      .prior 87 true [15, 1, 15],
      .prior 288 true [1, 15, 1, 15],
      .equation 137 false false
        [33, 0]
        [],
      .prior 290 false [],
      .prior 291 false [],
      .prior 298 false []]⟩,
    ⟨[203, 5], [203], [
      .prior 297 true [5],
      .prior 273 true [5],
      .prior 292 true [1, 5],
      .equation 26 false false
        [33, 0]
        [],
      .prior 290 false [],
      .prior 291 false [],
      .prior 298 false []]⟩,
    ⟨[33, 9], [33], [
      .prior 111 false [],
      .prior 112 false []]⟩,
    ⟨[33, 0], [203], [
      .prior 289 false [],
      .prior 298 false []]⟩,
    ⟨[203, 9], [203, 9], [
]⟩,
    ⟨[203], [203], [
]⟩,
    ⟨[203, 9], [203], [
      .prior 303 false [],
      .prior 298 true [9],
      .prior 273 true [9],
      .prior 301 true [1, 9],
      .equation 3 false false
        [33, 0]
        [],
      .prior 302 false [],
      .prior 304 false []]⟩,
    ⟨[37, 13], [37, 13], [
]⟩,
    ⟨[37, 13], [203], [
      .prior 306 false [],
      .equation 47 false false
        []
        [13],
      .prior 114 true [1, 13],
      .equation 40 false false
        [33, 0]
        [],
      .prior 302 false [],
      .prior 304 false []]⟩,
    ⟨[203, 13], [201], [
      .prior 230 false []]⟩,
    ⟨[201], [37], [
      .prior 308 true [],
      .prior 307 true [13],
      .equation 10 false false
        [37]
        []]⟩,
    ⟨[37, 15], [197], [
      .prior 129 true [15],
      .prior 309 true [5, 15],
      .prior 229 false [15],
      .prior 228 false []]⟩,
    ⟨[35, 11], [35, 11], [
]⟩,
    ⟨[35, 11], [35], [
      .prior 311 false [],
      .prior 114 true [11],
      .equation 139 false false
        [33, 10]
        [12, 10, 12],
      .equation 8 true false
        [33, 10]
        [12, 10, 12],
      .prior 271 false [12, 10, 12],
      .equation 10 true false
        [211, 12]
        [10, 12],
      .prior 287 false [10, 12],
      .equation 8 true false
        [211, 10]
        [12],
      .prior 234 false [12],
      .prior 272 false [12],
      .equation 10 true false
        [33, 12]
        [],
      .equation 46 true false
        []
        [],
      .prior 116 false []]⟩,
    ⟨[33, 11], [211], [
      .prior 271 false []]⟩,
    ⟨[203, 11], [203, 11], [
]⟩,
    ⟨[203, 11], [203], [
      .prior 314 false [],
      .prior 298 true [11],
      .prior 273 true [11],
      .prior 272 true [1, 11],
      .prior 234 true [1, 11],
      .prior 277 true [11, 1, 11],
      .prior 313 true [1, 11, 1, 11],
      .equation 43 false false
        [33, 0]
        [],
      .prior 302 false [],
      .prior 304 false []]⟩,
    ⟨[203, 15], [203], [
      .prior 299 false []]⟩,
    ⟨[203, 13], [37], [
      .prior 308 false [],
      .prior 309 false []]⟩,
    ⟨[197], [37], [
      .equation 10 true false
        [197]
        [],
      .prior 310 true [13, 13],
      .prior 309 true [15, 13, 13],
      .prior 230 true [15, 13, 13],
      .prior 316 true [13, 15, 13, 13],
      .equation 138 false false
        [203, 12]
        [13, 13],
      .prior 304 false [13],
      .prior 317 false []]⟩,
    ⟨[37, 11], [195], [
      .prior 318 true [11],
      .prior 227 false []]⟩,
    ⟨[203, 10], [203], [
      .equation 8 true false
        [203, 10]
        [],
      .prior 315 false []]⟩,
    ⟨[195, 13], [195, 13], [
]⟩,
    ⟨[195], [195], [
]⟩,
    ⟨[195, 13], [195], [
      .prior 321 false [],
      .prior 319 true [13],
      .prior 317 true [11, 13],
      .equation 139 false false
        [203, 10]
        [12, 10],
      .prior 320 false [12, 10],
      .equation 10 true false
        [203, 12]
        [10],
      .prior 230 false [10],
      .prior 309 false [10],
      .equation 8 true false
        [37, 10]
        [],
      .prior 319 false [],
      .prior 322 false []]⟩,
    ⟨[37, 1], [35], [
      .prior 124 false []]⟩,
    ⟨[37, 10], [195], [
      .equation 8 true false
        [37, 10]
        [],
      .prior 319 false []]⟩,
    ⟨[195, 1], [195, 1], [
]⟩,
    ⟨[195, 1], [195], [
      .prior 326 false [],
      .prior 319 true [1],
      .equation 47 false false
        []
        [11, 1],
      .prior 312 true [1, 11, 1],
      .prior 324 true [11, 1, 11, 1],
      .equation 43 false false
        [37]
        [10],
      .prior 325 false [],
      .prior 322 false []]⟩,
    ⟨[37, 5], [37], [
      .prior 127 false [],
      .prior 129 false []]⟩,
    ⟨[195, 5], [195, 5], [
]⟩,
    ⟨[195, 5], [195], [
      .prior 329 false [],
      .prior 319 true [5],
      .prior 328 true [11, 5],
      .equation 28 false false
        [37]
        [10],
      .prior 325 false [],
      .prior 322 false []]⟩,
    ⟨[37, 7], [37], [
      .prior 131 false [],
      .prior 132 false []]⟩,
    ⟨[195, 7], [195, 7], [
]⟩,
    ⟨[37, 9], [37], [
      .prior 134 false [],
      .prior 135 false []]⟩,
    ⟨[195, 9], [195, 9], [
]⟩,
    ⟨[41, 3], [41, 3], [
]⟩,
    ⟨[41, 3], [195], [
      .prior 335 false [],
      .equation 49 false false
        []
        [3],
      .prior 137 true [11, 3],
      .equation 34 false false
        [37]
        [10],
      .prior 325 false [],
      .prior 322 false []]⟩,
    ⟨[195, 3], [193], [
      .prior 226 false []]⟩,
    ⟨[193], [41], [
      .prior 337 true [],
      .prior 336 true [3],
      .equation 4 false false
        [41]
        []]⟩,
    ⟨[41, 1], [191], [
      .prior 338 true [1],
      .prior 225 false []]⟩,
    ⟨[197], [37], [
      .prior 318 false []]⟩,
    ⟨[39, 15], [39, 15], [
]⟩,
    ⟨[39, 15], [39], [
      .prior 341 false [],
      .prior 137 true [15],
      .equation 36 false false
        [37]
        [14, 2],
      .equation 12 true false
        [37, 14]
        [2],
      .prior 310 false [2],
      .prior 340 false [2],
      .equation 4 true false
        [37, 2]
        [],
      .equation 48 true false
        []
        [],
      .prior 139 false []]⟩,
    ⟨[37, 15], [37], [
      .prior 310 false [],
      .prior 340 false []]⟩,
    ⟨[195, 15], [195, 15], [
]⟩,
    ⟨[195, 15], [195], [
      .prior 344 false [],
      .prior 319 true [15],
      .prior 343 true [11, 15],
      .equation 136 false false
        [37, 10]
        [],
      .prior 325 false [],
      .prior 322 false []]⟩,
    ⟨[195, 13], [195], [
      .prior 321 false [],
      .prior 323 false []]⟩,
    ⟨[193], [41], [
      .prior 338 false []]⟩,
    ⟨[195, 2], [41], [
      .equation 4 true false
        [195, 2]
        [],
      .prior 226 false [],
      .prior 347 false []]⟩,
    ⟨[41, 13], [41, 13], [
]⟩,
    ⟨[41, 13], [41], [
      .prior 349 false [],
      .prior 347 true [13],
      .prior 226 true [13],
      .prior 346 true [3, 13],
      .equation 35 false false
        [195, 2]
        [],
      .prior 348 false [],
      .prior 148 false []]⟩,
    ⟨[195, 1], [195], [
      .prior 326 false [],
      .prior 327 false []]⟩,
    ⟨[191], [191], [
]⟩,
    ⟨[41, 3], [195], [
      .prior 335 false [],
      .prior 336 false []]⟩,
    ⟨[43], [41], [
      .equation 50 false false
        []
        [],
      .prior 347 true [15],
      .prior 226 true [15],
      .prior 345 true [3, 15],
      .prior 353 true [15, 3, 15],
      .equation 36 false false
        [41]
        [],
      .prior 148 true []]⟩,
    ⟨[43], [41], [
      .prior 354 false []]⟩,
    ⟨[41, 5], [45], [
      .prior 354 true [5],
      .equation 51 true false
        []
        []]⟩,
    ⟨[41, 11], [39], [
      .prior 145 false []]⟩,
    ⟨[41, 0], [191], [
      .equation 2 true false
        [41, 0]
        [],
      .prior 339 false []]⟩,
    ⟨[41, 7], [41], [
      .prior 147 false [],
      .prior 147 false [],
      .prior 146 true [7],
      .equation 21 false false
        [39, 6]
        [10],
      .equation 17 true false
        [39, 6]
        [10],
      .prior 142 false [10],
      .equation 8 true false
        [39, 10]
        [],
      .equation 49 true false
        []
        [],
      .prior 148 false []]⟩,
    ⟨[41, 1], [191], [
      .prior 339 false []]⟩,
    ⟨[191], [189], [
      .prior 360 true [],
      .prior 148 true [1],
      .equation 18 true false
        [41, 0]
        [1, 1],
      .prior 359 false [1, 7, 1, 1],
      .prior 339 false [7, 1, 1],
      .prior 224 false [1, 1],
      .equation 2 false false
        [189]
        []]⟩,
    ⟨[191], [189], [
      .prior 361 false []]⟩,
    ⟨[41, 9], [41], [
      .prior 149 false [],
      .prior 150 false []]⟩,
    ⟨[41, 15], [41], [
      .prior 151 false [],
      .prior 355 false []]⟩,
    ⟨[41, 4], [45], [
      .equation 6 true false
        [41, 4]
        [],
      .prior 356 false []]⟩,
    ⟨[45, 15], [45, 15], [
]⟩,
    ⟨[45, 15], [45], [
      .prior 366 false [],
      .prior 356 true [15],
      .prior 364 true [5, 15],
      .equation 30 false false
        [41, 4]
        [],
      .prior 365 false [],
      .prior 154 false []]⟩,
    ⟨[45, 3], [45, 3], [
]⟩,
    ⟨[45, 3], [45], [
      .prior 368 false [],
      .prior 356 true [3],
      .prior 347 true [5, 3],
      .prior 226 true [5, 3],
      .prior 330 true [3, 5, 3],
      .prior 353 true [5, 3, 5, 3],
      .equation 33 false false
        [41]
        [4],
      .prior 365 false [],
      .prior 154 false []]⟩,
    ⟨[41, 1], [189], [
      .prior 360 false [],
      .prior 362 false []]⟩,
    ⟨[187, 1], [187, 1], [
]⟩,
    ⟨[187, 1], [41], [
      .prior 371 false [],
      .prior 223 true [1],
      .prior 370 true [13, 1],
      .equation 40 false false
        [41]
        [12],
      .equation 10 true false
        [41, 12]
        [],
      .prior 350 false [],
      .prior 148 false []]⟩,
    ⟨[189], [187], [
      .prior 370 true [],
      .prior 372 true [1],
      .equation 2 false false
        [187]
        []]⟩,
    ⟨[191], [187], [
      .prior 362 false [],
      .prior 373 false []]⟩,
    ⟨[187, 7], [187], [
      .prior 373 true [7],
      .equation 124 true false
        []
        [],
      .prior 374 false []]⟩,
    ⟨[189], [187], [
      .prior 373 false []]⟩,
    ⟨[187, 3], [187], [
      .prior 373 true [3],
      .prior 361 true [3],
      .prior 339 true [3],
      .prior 347 true [1, 3],
      .prior 226 true [1, 3],
      .prior 351 true [3, 1, 3],
      .equation 39 false false
        [195]
        [2, 0],
      .prior 348 false [0],
      .equation 2 true false
        [41, 0]
        [],
      .prior 339 false [],
      .prior 352 false [],
      .prior 362 false [],
      .prior 376 false []]⟩,
    ⟨[187, 11], [187], [
      .prior 373 true [11],
      .prior 361 true [11],
      .prior 339 true [11],
      .equation 49 false false
        []
        [1, 11],
      .prior 140 true [11, 1, 11],
      .prior 357 true [1, 11, 1, 11],
      .equation 43 false false
        [41, 0]
        [],
      .prior 358 false [],
      .prior 352 false [],
      .prior 362 false [],
      .prior 376 false []]⟩,
    ⟨[187, 1], [41], [
      .prior 371 false [],
      .prior 372 false []]⟩,
    ⟨[187, 4], [185], [
      .equation 6 true false
        [187, 4]
        [],
      .prior 222 false []]⟩,
    ⟨[45, 1], [45, 1], [
]⟩,
    ⟨[185], [185], [
]⟩,
    ⟨[45, 1], [185], [
      .prior 381 false [],
      .prior 356 true [1],
      .prior 379 true [5, 1],
      .equation 26 false false
        [187]
        [4],
      .prior 380 false [],
      .prior 382 false []]⟩]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
