/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal E8 Coxeter rewrite chunks in the original C431 alphabet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431CoxeterRewrites

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Exact bounded chunks of literal E8 square, commutation and braid moves, block 8. -/
def y431E8RewriteData08 : Fin 64 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
![
  ([3, 6, 5, 1, 2, 3, 0, 1, 8, 0, 5, 2, 1, 0, 8, 6, 3, 0, 2, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5,
    6], [3, 6, 5, 1, 2, 0, 1, 8, 0, 5, 0, 6, 8, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 0, 1, 0],
    [.commute 17, .braid 18, .commute 20, .braid 21, .commute 23, .commute 24, .square 25,
    .commute 20, .commute 21, .commute 19, .braid 17, .braid 19, .braid 21, .commute 23,
    .commute 24, .braid 25, .commute 27, .commute 14, .commute 15, .commute 16, .commute 17,
    .commute 13, .commute 14, .commute 12, .commute 13, .braid 14, .commute 16, .braid 17,
    .commute 19, .commute 20, .braid 21, .braid 23, .commute 25, .commute 26, .commute 11,
    .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .braid 11, .commute
    13, .braid 14, .commute 16, .braid 17, .braid 19, .commute 21, .commute 22, .braid 23,
    .commute 25, .commute 18, .commute 15, .commute 16, .commute 17, .commute 12, .commute 13,
    .commute 14, .commute 15, .commute 16, .commute 13, .commute 11, .commute 12, .commute 10])
,
  ([3, 6, 5, 1, 2, 0, 1, 8, 0, 5, 0, 6, 8, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 0, 1, 0], [6,
    1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 0, 1, 0],
    [.commute 11, .braid 8, .commute 10, .commute 7, .braid 8, .commute 6, .commute 2, .commute
    3, .braid 4, .braid 6, .commute 8, .commute 3, .commute 4, .commute 0, .commute 1, .commute
    2, .commute 3])
,
  ([0, 1, 0, 6, 5, 0, 1, 8, 0, 1, 2, 3, 5, 0, 1, 2, 6, 5, 0, 1, 8, 0, 1, 2, 3, 5, 0, 1, 6], [0,
    6, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 5, 1, 2, 3, 2, 0, 1],
    [.commute 27, .commute 26, .commute 11, .commute 12, .commute 13, .commute 10, .commute 11,
    .commute 9, .commute 2, .braid 3, .commute 5, .commute 6, .braid 7, .braid 9, .braid 11,
    .braid 13, .commute 15, .commute 16, .commute 17, .commute 18, .commute 19, .commute 20,
    .commute 21, .braid 22, .commute 24, .commute 25, .commute 23, .commute 24, .commute 22,
    .commute 23, .commute 21, .commute 22, .commute 8, .commute 5, .braid 6, .braid 8, .commute
    10, .commute 11, .commute 12, .commute 13, .braid 14, .commute 16, .commute 17, .commute 18,
    .commute 19, .braid 20, .commute 17, .commute 13, .commute 14, .commute 15, .commute 16,
    .commute 12, .commute 13, .commute 14, .commute 15, .commute 11, .commute 12, .commute 10,
    .commute 11, .commute 9, .commute 7, .commute 8, .commute 1, .commute 2])
,
  ([0, 6, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 5, 1, 2, 3, 2, 0, 1], [6,
    0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 5, 1, 2, 3, 2, 0, 1],
    [.commute 0])
,
  ([3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 0, 1, 0, 6, 0, 5, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 5, 1, 2, 3, 2, 0, 1], [1, 2, 3, 0, 5, 6, 5, 3, 2, 0,
    1], [.commute 18, .commute 19, .commute 20, .square 21, .square 20, .braid 16, .commute 18,
    .square 19, .square 18, .square 17, .commute 15, .square 16, .commute 10, .commute 11,
    .commute 12, .braid 13, .square 15, .square 14, .commute 7, .commute 8, .commute 9, .commute
    10, .commute 11, .commute 12, .square 13, .commute 8, .commute 9, .braid 10, .square 12,
    .square 11, .commute 6, .commute 7, .commute 8, .commute 9, .square 10, .commute 6, .braid
    7, .square 9, .square 8, .commute 5, .commute 6, .square 7, .commute 4, .commute 5, .square
    6, .braid 4, .square 6, .commute 3, .commute 4, .braid 1, .commute 3, .braid 4, .square 6,
    .commute 5, .commute 6, .commute 7, .square 8, .commute 0, .braid 1, .commute 3, .commute 4,
    .commute 5, .commute 6, .square 7])
,
  ([1, 2, 3, 0, 5, 6, 5, 3, 2, 0, 1], [1, 0, 5, 6, 5, 0, 1], [.commute 2, .commute 3, .commute
    4, .commute 5, .square 6, .commute 1, .commute 2, .commute 3, .commute 4, .square 5])
,
  ([5, 3], [5, 3], [])
,
  ([3, 5, 3], [5], [.commute 0, .square 1])
,
  ([1, 0, 5, 6, 5, 0, 1, 2, 3, 2], [1, 0, 5, 6, 5, 0, 1, 2, 3, 2], [])
,
  ([1, 0, 5, 6, 5, 0, 1, 2, 3, 2, 1, 0, 5, 6, 5, 0, 1], [3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3],
    [.braid 2, .commute 4, .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .commute
    10, .braid 11, .square 13, .commute 1, .braid 2, .commute 4, .commute 5, .commute 6,
    .commute 7, .commute 8, .braid 9, .commute 11, .square 12, .commute 0, .commute 1, .braid 2,
    .commute 4, .commute 5, .commute 6, .braid 7, .commute 9, .commute 10, .square 11, .braid 4,
    .commute 6, .commute 7, .commute 8, .commute 9, .commute 3, .braid 4, .commute 6, .commute
    7, .commute 8, .commute 2, .commute 3, .braid 4, .commute 6, .commute 7, .commute 1,
    .commute 2, .commute 3, .braid 4, .commute 6, .commute 0, .commute 1, .commute 2, .commute
    3, .braid 4])
,
  ([2, 1], [2, 1], [])
,
  ([1, 2], [1, 2], [])
,
  ([1, 2, 1], [1, 2, 1], [])
,
  ([1, 2, 1, 1, 0, 8, 1], [1, 0, 8, 2, 1], [.square 2, .commute 1, .commute 2])
,
  ([1, 2, 8, 0, 1], [8, 1, 2, 0, 1], [.commute 1, .commute 0])
,
  ([8, 1, 2, 0, 1, 1, 0, 8, 0, 1], [1, 2, 0, 1], [.square 4, .square 3, .commute 0, .commute 1,
    .square 2])
,
  ([1, 0, 2, 1], [1, 2, 0, 1], [.commute 1])
,
  ([1, 0, 8, 0, 1, 5], [1, 0, 8, 0, 5, 1], [.commute 4])
,
  ([1, 0, 8, 0, 5, 1, 1, 0, 8, 0, 1], [5, 1, 0, 8, 0, 5, 1], [.square 5, .braid 1, .commute 3,
    .braid 4, .square 6, .braid 2, .commute 4, .commute 1, .braid 2, .commute 0])
,
  ([5, 1, 0, 8, 0, 5, 1, 8, 1, 2, 0, 1], [8, 1, 0, 5, 2, 1], [.braid 2, .commute 4, .commute 5,
    .square 6, .square 5, .commute 0, .commute 1, .braid 2, .commute 4, .square 5, .commute 0])
,
  ([1, 2, 5, 0, 1, 8], [5, 1, 0, 8, 2, 1], [.commute 4, .commute 1, .commute 2, .commute 3,
    .commute 0])
,
  ([5, 1, 0, 8, 2, 1, 8, 1, 2, 0, 1], [5], [.commute 3, .commute 4, .square 5, .square 4,
    .square 3, .square 2, .square 1])
,
  ([0, 1, 0, 1, 2, 0, 1], [1, 2, 1], [.braid 0, .square 2, .commute 1, .square 2])
,
  ([1, 2, 1, 1, 2, 0, 1], [0, 1, 0], [.square 2, .square 1, .braid 0])
,
  ([5, 1, 0, 8, 0, 1], [5, 1, 0, 8, 0, 1], [])
,
  ([1, 5, 0, 8, 0, 1, 5], [5, 1, 0, 8, 0, 5, 1], [.commute 5, .commute 0])
,
  ([3, 5], [5, 3], [.commute 0])
,
  ([5, 3, 3], [5], [.square 1])
,
  ([1, 3, 1], [3], [.commute 0, .square 1])
,
  ([1, 1, 0, 8, 1], [0, 8, 1], [.square 0])
,
  ([1, 0, 8, 1], [1, 0, 8, 1], [])
,
  ([1, 0, 8, 1, 8, 1, 2, 0, 1], [1, 2, 1], [.commute 2, .square 3, .square 2, .commute 1,
    .square 2])
,
  ([1, 2, 1, 0, 8, 1], [2, 1, 0, 8, 2, 1], [.braid 0, .commute 2, .commute 3])
,
  ([1, 2, 8, 0, 1, 2], [8, 0, 1, 2, 0, 1], [.commute 1, .commute 2, .braid 3, .commute 0, .braid
    1, .commute 3])
,
  ([1, 0, 8, 2, 1, 8, 0, 1, 2, 0, 1], [2], [.commute 2, .commute 3, .square 4, .commute 1,
    .braid 2, .square 4, .braid 0, .commute 2, .square 3, .square 2, .square 1])
,
  ([1, 0, 8, 2, 1, 1, 0, 8, 0, 1], [8, 1, 2, 1], [.square 4, .commute 2, .commute 1, .braid 2,
    .square 4, .square 3, .commute 1, .commute 0])
,
  ([8, 1, 2, 1, 8, 1, 2, 0, 1], [0, 1, 0], [.commute 0, .commute 1, .commute 2, .square 3,
    .square 2, .square 1, .braid 0])
,
  ([0, 1, 0, 2], [0, 1, 2, 0], [.commute 2])
,
  ([0, 2, 1, 0], [2, 0, 1, 0], [.commute 0])
,
  ([2, 0, 1, 0, 2], [0, 1, 2, 1, 0], [.commute 3, .commute 0, .braid 1])
,
  ([2, 5], [5, 2], [.commute 0])
,
  ([1, 0, 8, 0, 1, 5, 2], [1, 0, 8, 0, 5, 1, 2], [.commute 4])
,
  ([2, 1, 5, 0, 8, 0, 1], [5, 2, 1, 0, 8, 0, 1], [.commute 1, .commute 0])
,
  ([2, 1, 0, 8, 0, 1], [2, 1, 0, 8, 0, 1], [])
,
  ([1, 0, 8, 0, 1, 2, 1, 0, 8, 0, 1], [2, 1, 0, 8, 0, 1, 2], [.braid 1, .commute 3, .commute 4,
    .commute 5, .braid 6, .square 8, .commute 0, .braid 1, .commute 3, .braid 4, .commute 6,
    .square 7, .braid 2, .commute 4, .commute 5, .commute 1, .braid 2, .commute 4, .commute 0,
    .commute 1, .braid 2])
,
  ([0, 1, 2, 1, 0, 5], [2, 1, 0, 5, 1, 2], [.braid 1, .commute 3, .commute 4, .commute 0, .braid
    1, .commute 3])
,
  ([2, 1, 5, 0, 1, 2], [5, 0, 1, 2, 1, 0], [.commute 1, .braid 2, .commute 4, .commute 0,
    .commute 1, .braid 2])
,
  ([5, 0, 1, 2, 1, 0, 5], [2, 1, 0, 5, 0, 1, 2], [.braid 2, .commute 4, .commute 5, .commute 1,
    .braid 2, .commute 4, .commute 0, .commute 1, .braid 2])
,
  ([1, 2, 1, 1, 0, 8, 0, 5, 1, 2], [1, 0, 8, 0, 5, 1, 2, 1], [.square 2, .commute 1, .commute 2,
    .commute 3, .commute 4, .braid 5])
,
  ([5, 2, 1, 0, 8, 0, 1, 1, 0, 8, 0, 5, 1, 2, 1], [1], [.square 6, .square 5, .square 4, .square
    3, .commute 0, .commute 1, .square 2, .square 1, .square 0])
,
  ([2, 1, 0, 8, 0, 1, 2, 5, 1, 0, 8, 0, 5, 1], [8, 1, 0, 5, 2, 1, 0, 8, 2, 1], [.braid 2,
    .commute 4, .commute 5, .commute 6, .commute 7, .braid 8, .square 10, .commute 6, .commute
    1, .braid 2, .commute 4, .commute 0, .commute 1, .braid 2, .braid 4, .braid 6, .commute 8,
    .square 9, .commute 3, .braid 1, .braid 3, .commute 5, .commute 6, .commute 7, .commute 4,
    .commute 3])
,
  ([1, 2, 8, 0, 1, 2, 5, 0, 1, 8], [8, 1, 0, 5, 2, 1, 0, 8, 2, 1], [.commute 8, .commute 5,
    .commute 6, .commute 7, .commute 4, .commute 1, .commute 2, .commute 3, .commute 0])
,
  ([2, 1, 0, 5, 0, 1, 2], [2, 1, 0, 5, 0, 1, 2], [])
,
  ([5, 2, 1, 0, 8, 0, 1, 8, 1, 0, 5, 2, 1, 0, 8, 2, 1], [1, 0, 8, 0, 1], [.braid 3, .commute 5,
    .square 6, .square 5, .square 4, .commute 0, .commute 1, .commute 2, .square 3, .commute 1,
    .commute 0, .braid 1, .square 3, .commute 2, .commute 3, .square 4, .commute 0, .braid 1])
,
  ([1, 2, 1, 0, 5, 0, 1, 2], [2, 1, 0, 5, 0, 1, 2, 1], [.braid 0, .commute 2, .commute 3,
    .commute 4, .braid 5])
,
  ([2, 1, 0, 5, 0, 1, 2, 1, 1, 0, 8, 0, 1], [0, 5, 2, 1, 0, 8, 5, 1, 2, 0, 1], [.square 7,
    .commute 6, .commute 7, .braid 4, .commute 6, .commute 3, .braid 1, .braid 3, .commute 5,
    .commute 2, .commute 0, .commute 1])
,
  ([1, 0, 2, 1, 5, 8, 0, 1, 2, 5, 0], [1, 0, 8, 2, 1, 0, 5, 0, 1, 2, 0], [.commute 8, .commute
    7, .commute 4, .braid 5, .commute 3, .commute 2])
,
  ([0, 1, 0, 8, 1, 0, 5, 2, 1, 0, 8, 2, 1], [8, 1, 0, 5, 2, 1, 0, 8, 2, 0, 1], [.braid 0,
    .commute 2, .square 3, .braid 1, .commute 3, .commute 4, .commute 5, .braid 6, .commute 8,
    .commute 0])
,
  ([8, 1, 0, 5, 2, 1, 0, 8, 2, 0, 1, 1, 0, 8, 2, 1, 0, 5, 0, 1, 2, 0], [8, 5, 2, 1], [.square
    10, .square 9, .commute 7, .square 8, .square 7, .braid 5, .square 7, .commute 3, .commute
    2, .braid 3, .commute 5, .square 6, .braid 4, .square 6, .commute 2, .commute 1, .braid 2,
    .commute 4, .square 5, .square 4])
,
  ([8, 1, 0, 5, 2, 1, 0, 8, 2, 1, 8, 5, 2, 1], [8, 2, 1, 0, 5, 0, 1, 2, 1, 0], [.commute 7,
    .commute 8, .square 9, .commute 8, .commute 7, .braid 8, .square 10, .commute 3, .commute 4,
    .braid 5, .commute 2, .braid 3, .commute 5, .braid 6, .commute 8, .braid 1, .commute 3,
    .commute 4, .commute 5, .braid 6])
,
  ([0, 1, 2, 1, 0, 5, 0, 1, 2, 8], [0, 5, 2, 1, 0, 8, 5, 1, 2, 1], [.braid 1, .commute 3,
    .commute 4, .commute 5, .braid 6, .commute 8, .commute 7, .commute 6, .braid 3, .commute 5,
    .commute 2, .commute 1])
,
  ([0, 5, 2, 1, 0, 8, 5, 1, 2, 1, 5, 1, 0, 8, 0, 5, 1], [5, 0, 8, 1, 2], [.commute 6, .commute
    7, .commute 8, .square 9, .square 8, .commute 5, .commute 6, .braid 3, .commute 5, .braid 6,
    .square 8, .square 7, .commute 1, .commute 0, .braid 1, .commute 3, .commute 4, .commute 5,
    .square 6, .commute 0, .commute 1, .braid 2, .commute 4, .square 5, .commute 3, .commute 2])
,
  ([2, 1, 8, 0, 5], [8, 2, 1, 0, 5], [.commute 1, .commute 0])
,
  ([5, 1, 0, 8, 0, 5, 1, 8, 1, 0, 5, 2, 1, 0, 8, 2, 1], [2, 1, 0, 8, 0, 1, 2], [.braid 2,
    .commute 4, .commute 5, .square 6, .square 5, .commute 0, .commute 1, .braid 2, .square 4,
    .square 3, .commute 2, .braid 3, .commute 5, .commute 0, .braid 1, .commute 3, .commute 4,
    .braid 5, .square 7, .commute 0, .commute 1, .braid 2])
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
