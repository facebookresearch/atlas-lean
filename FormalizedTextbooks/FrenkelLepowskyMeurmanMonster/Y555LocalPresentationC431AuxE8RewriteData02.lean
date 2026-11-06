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
/-- Exact bounded chunks of literal E8 square, commutation and braid moves, block 2. -/
def y431AuxE8RewriteData02 : Fin 64 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
![
  ([1, 2, 1, 2, 1, 0, 8, 0, 1, 2], [0, 8, 0, 1, 2, 1], [.braid 0, .square 2, .square 1, .commute
    0, .commute 1, .commute 2, .braid 3])
,
  ([0, 8, 0, 1, 2, 1, 1, 2, 1], [0, 8, 0], [.square 5, .square 4, .square 3])
,
  ([1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 1, 5, 2, 1, 0, 8, 0, 5, 1, 2], [5, 2, 1, 0, 8, 0, 5, 1,
    2, 0, 1, 0], [.commute 12, .commute 10, .commute 11, .braid 12, .square 14, .commute 8,
    .braid 9, .braid 7, .commute 9, .braid 10, .commute 12, .square 13, .commute 6, .braid 4,
    .braid 6, .commute 8, .commute 2, .commute 1, .braid 2, .commute 4, .commute 5, .braid 6,
    .braid 8, .commute 10, .commute 11, .square 12, .commute 7, .braid 5, .braid 7, .commute 9,
    .commute 10, .braid 3, .commute 5, .commute 6, .braid 7, .commute 9, .braid 10, .square 12,
    .commute 9, .commute 10, .commute 8, .braid 6, .braid 8, .braid 10, .square 12, .commute 9,
    .commute 1, .commute 0, .braid 1, .commute 3, .commute 4, .commute 5, .commute 6, .braid 7,
    .braid 9])
,
  ([5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 1, 0, 1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 1], [0, 1, 0],
    [.braid 9, .square 11, .square 10, .commute 6, .commute 7, .commute 8, .square 9, .braid 6,
    .square 8, .square 7, .commute 5, .square 6, .commute 4, .square 5, .commute 3, .square 4,
    .commute 0, .commute 1, .commute 2, .square 3, .braid 0, .square 2, .square 1, .braid 0])
,
  ([2, 1, 0, 8, 0, 1, 2, 1, 2, 1], [2, 1, 0, 8, 2, 0], [.braid 5, .square 7, .square 6, .commute
    4])
,
  ([6, 5, 1, 0, 8, 0, 5, 6, 1, 2, 1, 0, 8, 0, 1, 2], [8, 6, 1, 0, 5, 2, 1, 0, 8, 6, 2, 1],
    [.braid 3, .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .braid 10, .square
    12, .braid 7, .commute 9, .commute 10, .commute 1, .commute 2, .braid 3, .commute 5,
    .commute 6, .braid 7, .commute 9, .braid 10, .square 12, .commute 5, .commute 6, .commute 7,
    .commute 8, .commute 1, .commute 0])
,
  ([8, 6, 1, 0, 5, 2, 1, 0, 8, 6, 2, 1, 1, 2, 1], [8, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1], [.square
    11, .square 10])
,
  ([0, 8, 0, 1, 2, 1, 8, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1], [6, 5, 1, 0, 8, 0, 5, 6, 1], [.braid 0,
    .commute 2, .commute 3, .commute 4, .square 5, .commute 4, .square 5, .commute 3, .commute
    4, .commute 5, .square 6, .commute 2, .commute 1, .braid 2, .commute 4, .square 5, .braid 3,
    .commute 5, .commute 0, .commute 1, .commute 2, .braid 3, .commute 1])
,
  ([2, 1, 0, 8, 0, 1, 2, 0, 1, 0], [2, 1, 0, 8, 0, 1, 2, 0, 1, 0], [])
,
  ([2, 1, 0, 8, 0, 1, 2, 0, 1, 0, 2, 1, 0, 8, 0, 1, 2], [0, 1, 0], [.commute 6, .braid 4, .braid
    6, .commute 8, .square 9, .commute 5, .braid 6, .square 8, .square 7, .commute 3, .commute
    4, .commute 5, .square 6, .braid 1, .commute 3, .commute 0, .braid 1, .braid 3, .square 5,
    .square 4, .commute 2, .square 3])
,
  ([2, 1, 0, 8, 0, 1, 2, 5, 1, 0, 8, 0, 5, 1], [8, 1, 0, 5, 2, 1, 0, 8, 2, 1], [.braid 2,
    .commute 4, .commute 5, .commute 6, .commute 7, .braid 8, .square 10, .commute 6, .commute
    1, .braid 2, .commute 4, .commute 0, .commute 1, .braid 2, .braid 4, .braid 6, .commute 8,
    .square 9, .commute 3, .braid 1, .braid 3, .commute 5, .commute 6, .commute 7, .commute 4,
    .commute 3])
,
  ([8, 1, 0, 5, 2, 1, 0, 8, 2, 1, 2, 1, 0, 8, 0, 1, 2], [5, 1, 0, 8, 0, 5, 1], [.braid 8,
    .square 10, .commute 7, .commute 8, .braid 5, .commute 7, .braid 8, .square 10, .square 9,
    .commute 4, .braid 5, .commute 7, .square 8, .commute 6, .square 7, .commute 5, .braid 2,
    .commute 4, .commute 0, .commute 1, .braid 2, .commute 0])
,
  ([1, 0, 5, 0, 1, 2, 1, 0, 8, 0, 1, 2], [1, 0, 5, 2, 1, 0, 8, 0, 1, 2, 0, 1], [.braid 4,
    .commute 6, .commute 7, .commute 8, .braid 9, .commute 3, .braid 4, .commute 6, .braid 7,
    .commute 9])
,
  ([1, 0, 5, 0, 1, 6, 5, 1, 0, 8, 0, 5, 6, 1], [6, 5, 1, 0, 8, 0, 5, 6, 0, 5, 0, 1], [.commute
    4, .commute 5, .square 6, .commute 3, .braid 4, .commute 6, .braid 7, .commute 9, .braid 2,
    .commute 4, .commute 5, .commute 6, .braid 7, .commute 1, .braid 2, .commute 4, .braid 5,
    .commute 7, .commute 0, .commute 1])
,
  ([6, 5, 1, 0, 8, 0, 5, 6, 0, 5, 0, 1, 0, 8, 0], [1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 6, 0, 1],
    [.braid 3, .commute 5, .commute 6, .commute 1, .commute 2, .braid 3, .commute 5, .braid 6,
    .commute 8, .commute 0, .commute 1, .commute 2, .braid 3, .commute 5, .braid 6, .braid 8,
    .commute 10, .braid 11, .square 13, .braid 9, .commute 11, .commute 8, .braid 9, .commute 4,
    .commute 5, .commute 3, .braid 1, .braid 3, .braid 5, .commute 7, .commute 8, .commute 9,
    .commute 4])
,
  ([1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 6, 0, 1, 1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 1], [1, 0, 8, 0,
    5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 0, 1], [.square 12, .square 11, .commute 9, .commute 10,
    .commute 11, .commute 12, .braid 13, .square 15, .commute 8, .commute 6, .commute 4,
    .commute 5, .braid 6, .braid 8, .commute 10, .braid 11, .commute 13, .commute 14, .square
    15, .commute 5, .commute 6, .braid 3, .commute 5, .braid 6, .commute 8, .braid 9, .commute
    11, .commute 12, .commute 13, .square 14])
,
  ([1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 0, 1, 5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2,
    1, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1], [8, 0, 1, 2, 5, 0, 5, 1, 8, 0, 5, 6, 5, 0, 8, 1, 0,
    5, 2, 1, 0, 8, 5, 6, 2, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1], [.commute 12,
    .commute 8, .commute 9, .braid 10, .braid 12, .commute 14, .commute 15, .commute 16,
    .commute 7, .braid 8, .commute 10, .commute 11, .braid 12, .commute 10, .braid 1, .commute
    3, .commute 4, .commute 5, .commute 6, .commute 7, .braid 8, .braid 10, .commute 12, .braid
    13, .commute 15, .braid 16, .commute 18, .commute 19, .commute 20, .braid 21, .square 23,
    .braid 11, .commute 13, .commute 14, .commute 15, .commute 10, .braid 11, .commute 13,
    .commute 9, .braid 7, .braid 9, .commute 11, .commute 12, .braid 13, .braid 15, .commute 17,
    .braid 18, .commute 20, .commute 21, .commute 22, .commute 23, .commute 4, .commute 5,
    .commute 6, .commute 7, .commute 8, .commute 9, .braid 10, .commute 3, .commute 4, .commute
    0, .braid 1, .commute 3, .braid 4])
,
  ([8, 0, 1, 2, 5, 0, 5, 1, 8, 0, 5, 6, 5, 0, 8, 1, 0, 5, 2, 1, 0, 8, 5, 6, 2, 1, 0, 5, 2, 1, 0,
    8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1], [8, 0, 1, 2, 5, 0, 1, 6, 5, 0, 8, 2, 1, 0, 5, 6, 0, 1, 2,
    0, 5, 0, 1, 8, 0, 5, 1, 8, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1], [.commute 6, .commute 7,
    .braid 8, .commute 10, .braid 11, .commute 13, .commute 14, .braid 15, .commute 17, .braid
    18, .commute 20, .commute 21, .commute 22, .braid 23, .commute 25, .commute 26, .square 27,
    .commute 20, .commute 21, .commute 22, .commute 23, .commute 16, .commute 17, .braid 18,
    .commute 20, .commute 21, .commute 15, .braid 16, .commute 18, .commute 19, .braid 14,
    .commute 16, .commute 17, .commute 18, .braid 19, .braid 21, .braid 23, .commute 25,
    .commute 26, .braid 9, .commute 11, .commute 12, .commute 13, .commute 14, .commute 15,
    .braid 16, .commute 18, .commute 19, .commute 8, .braid 9, .commute 11, .commute 12,
    .commute 13, .braid 14, .commute 16, .commute 7, .commute 8, .braid 9, .commute 11, .braid
    12, .commute 14, .commute 15, .braid 16, .commute 18])
,
  ([8, 0, 1, 2, 5, 0, 1, 6, 5, 0, 8, 2, 1, 0, 5, 6, 0, 1, 2, 0, 5, 0, 1, 8, 0, 5, 1, 8, 0, 8, 1,
    0, 5, 6, 0, 5, 0, 1, 2, 1], [8, 0, 5, 6, 0, 1, 2, 5, 0, 1, 0, 8, 5, 0, 1, 2, 6, 5, 0, 1, 6,
    5, 0, 8, 5, 0, 1, 6, 0, 5, 0, 1, 2, 1], [.braid 19, .commute 21, .commute 22, .braid 23,
    .commute 21, .commute 10, .commute 11, .commute 9, .commute 6, .commute 7, .commute 3,
    .commute 4, .commute 5, .commute 6, .braid 7, .braid 9, .braid 11, .commute 13, .commute 14,
    .commute 6, .commute 7, .commute 4, .commute 2, .commute 3, .braid 4, .commute 6, .braid 7,
    .commute 9, .commute 10, .braid 11, .commute 13, .braid 14, .commute 16, .commute 17,
    .commute 18, .braid 19, .braid 21, .commute 23, .braid 24, .braid 26, .square 28, .commute
    25, .braid 26, .square 28, .braid 22, .commute 24, .commute 20, .commute 21, .braid 22,
    .braid 24, .commute 26, .square 27, .commute 13, .commute 14, .commute 15, .commute 16,
    .commute 12, .braid 10, .braid 12, .commute 14, .commute 15, .braid 16, .commute 18,
    .commute 19])
,
  ([8, 0, 5, 6, 0, 1, 2, 5, 0, 1, 0, 8, 5, 0, 1, 2, 6, 5, 0, 1, 6, 5, 0, 8, 5, 0, 1, 6, 0, 5, 0,
    1, 2, 1], [8, 5, 0, 6, 5, 2, 6, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 2, 1, 0, 2,
    1], [.braid 8, .commute 10, .commute 11, .braid 12, .commute 14, .commute 15, .braid 16,
    .commute 18, .braid 19, .commute 21, .commute 22, .commute 6, .commute 5, .braid 6, .commute
    8, .commute 9, .commute 10, .commute 11, .braid 12, .commute 14, .commute 15, .braid 16,
    .commute 18, .braid 19, .commute 21, .braid 22, .commute 24, .commute 25, .square 26,
    .commute 17, .commute 18, .commute 16, .braid 14, .braid 16, .braid 18, .commute 20,
    .commute 21, .commute 22, .braid 23, .square 25, .commute 24, .braid 22, .braid 24, .square
    26, .commute 13, .commute 14, .commute 15, .commute 16, .commute 12, .commute 13, .braid 10,
    .commute 12, .braid 13, .commute 15, .braid 16, .commute 18, .commute 19, .commute 20,
    .commute 21, .commute 22, .commute 3, .braid 1, .braid 3, .commute 5])
,
  ([8, 5, 0, 6, 5, 2, 6, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 2, 1, 0, 2, 1], [5, 6,
    0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 0, 1, 0], [.commute 6,
    .commute 7, .commute 8, .commute 9, .braid 10, .commute 12, .braid 13, .commute 15, .braid
    16, .commute 18, .commute 19, .braid 7, .commute 9, .commute 10, .commute 11, .commute 4,
    .commute 5, .commute 6, .braid 7, .commute 9, .commute 5, .commute 2, .commute 3, .commute
    0, .commute 1, .commute 2, .braid 3, .braid 5, .commute 7, .commute 8, .braid 9, .braid 11,
    .commute 13, .commute 14, .commute 15, .braid 16, .commute 18, .braid 19, .commute 21,
    .braid 22, .commute 24, .square 25, .braid 23, .commute 10, .commute 8, .commute 9, .braid
    6, .commute 8, .commute 4, .commute 5, .braid 6, .commute 4, .commute 2, .commute 3])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 0, 1, 0, 1], [5, 6, 0,
    5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 1, 0], [.braid 23, .square 25])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 1, 0, 8], [2, 6, 5, 0,
    8, 1, 6, 0, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 1, 2, 0, 1, 8, 0, 8], [.commute 17, .commute
    18, .commute 16, .commute 15, .braid 16, .braid 18, .commute 20, .commute 21, .commute 22,
    .commute 13, .commute 10, .commute 11, .commute 12, .braid 13, .commute 11, .commute 9,
    .commute 10, .braid 11, .commute 13, .braid 14, .commute 16, .commute 17, .braid 18,
    .commute 20, .commute 16, .braid 6, .commute 8, .commute 9, .commute 5, .braid 6, .commute
    8, .braid 9, .commute 11, .commute 12, .commute 13, .braid 14, .braid 16, .commute 18,
    .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .commute 14,
    .commute 7, .braid 5, .braid 7, .commute 9, .commute 10, .commute 11, .commute 3, .commute
    2, .braid 3, .commute 5, .commute 6, .braid 7, .commute 9, .commute 1, .commute 0, .braid 1,
    .commute 3, .commute 4, .commute 5])
,
  ([2, 6, 5, 0, 8, 1, 6, 0, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 1, 2, 0, 1, 8, 0, 8], [2, 6, 0, 5,
    8, 1, 0, 8, 1, 5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 1, 0], [.commute 6, .braid 7, .braid
    9, .braid 11, .commute 13, .braid 14, .commute 16, .commute 17, .braid 18, .braid 20, .braid
    22, .square 24, .commute 21, .commute 19, .commute 20, .commute 17, .braid 15, .braid 17,
    .commute 19, .commute 13, .commute 12, .braid 13, .commute 15, .commute 16, .braid 17,
    .commute 15, .commute 10, .commute 11, .commute 12, .braid 13, .braid 15, .commute 17,
    .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .braid 6, .commute 8,
    .commute 9, .commute 10, .commute 5, .braid 6, .commute 8, .commute 4, .braid 2, .braid 4,
    .commute 6, .commute 7, .braid 8, .braid 10, .braid 12, .commute 14, .commute 15, .commute
    16, .commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 10,
    .braid 5, .commute 7])
,
  ([2, 6, 0, 5, 8, 1, 0, 8, 1, 5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 1, 0], [6, 0, 5, 2, 1, 0,
    8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 1, 0], [.commute 8, .commute 9, .commute 4,
    .braid 5, .commute 0, .commute 1, .commute 2])
,
  ([6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 1, 0, 2], [6, 0, 5, 2, 1,
    0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 1, 2, 1, 0], [.commute 23, .braid 21])
,
  ([6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 1, 2, 1, 0, 0], [6, 0, 5, 2,
    1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 1, 2, 1], [.square 24])
,
  ([6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 1, 2, 1, 5], [6, 0, 5, 2, 1,
    0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 1, 2, 0, 1], [.commute 20, .commute 21, .commute
    22, .square 23, .braid 18, .commute 20])
,
  ([6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 1, 2, 0, 1, 1], [6, 0, 5, 2, 1, 0,
    8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 1, 2, 0], [.square 22])
,
  ([6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 1, 2, 0, 8], [0, 8, 5, 6, 0, 5, 2,
    1, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1, 0], [.commute 16, .commute 15, .braid 16, .commute
    18, .commute 19, .commute 14, .commute 15, .braid 16, .commute 18, .braid 19, .square 21,
    .commute 13, .commute 14, .commute 15, .braid 16, .commute 18, .commute 17, .commute 16,
    .braid 14, .commute 9, .commute 10, .braid 11, .commute 8, .braid 9, .commute 11, .braid 12,
    .commute 14, .braid 5, .commute 7, .commute 4, .braid 5, .braid 7, .commute 9, .commute 10,
    .commute 11, .braid 12, .braid 9, .commute 11, .commute 12, .commute 8, .braid 9, .commute
    11, .commute 7, .commute 8, .braid 9, .commute 6, .commute 7, .commute 5, .commute 2,
    .commute 3, .commute 0, .commute 1, .commute 2, .braid 3, .braid 5, .braid 7, .commute 9,
    .commute 1, .commute 2, .commute 3, .commute 4, .commute 5])
,
  ([0, 8, 5, 6, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1, 0, 6], [0, 8, 5, 6, 0, 5, 2, 1,
    0, 8, 5, 6, 1, 0, 5, 0, 1, 2, 1, 0], [.commute 13, .braid 11, .braid 13, .commute 15,
    .commute 16, .commute 17, .commute 18, .commute 19, .square 20, .commute 12, .commute 10,
    .commute 11])
,
  ([0, 8, 5, 6, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 0, 1, 2, 1, 0, 2], [0, 8, 5, 6, 0, 5, 2, 1, 0,
    8, 5, 6, 1, 0, 5, 2, 0, 1, 0], [.braid 16, .commute 18, .square 19, .commute 15])
,
  ([0, 8, 5, 6, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 0, 1, 0, 0], [0, 8, 5, 6, 0, 5, 2, 1, 0, 8,
    5, 6, 1, 0, 5, 2, 0, 1], [.square 18])
,
  ([0, 8, 5, 6, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 0, 1, 5], [0, 8, 5, 6, 0, 5, 2, 1, 0, 8, 5,
    6, 5, 1, 2, 0, 1], [.commute 14, .commute 13, .braid 14, .commute 16, .square 17, .commute
    13, .commute 12])
,
  ([0, 8, 5, 6, 0, 5, 2, 1, 0, 8, 5, 6, 5, 1, 2, 0, 1, 1], [0, 8, 5, 6, 0, 5, 2, 1, 0, 8, 5, 6,
    5, 1, 2, 0], [.square 16])
,
  ([0, 8, 5, 6, 0, 5, 2, 1, 0, 8, 5, 6, 5, 1, 2, 0, 8], [8, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 1,
    2, 0], [.commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .commute 5, .commute
    6, .braid 7, .commute 9, .commute 3, .commute 4, .commute 5, .commute 6, .braid 7, .braid 9,
    .commute 3, .braid 4, .commute 6, .commute 7, .commute 2, .commute 3, .braid 4, .commute 6,
    .braid 7, .commute 9, .braid 10, .commute 12, .braid 13, .square 15, .commute 12, .commute
    11, .braid 8, .commute 10, .commute 6, .commute 5, .braid 6, .commute 8, .commute 9, .braid
    3, .commute 5, .braid 6, .commute 8, .commute 1, .commute 0, .braid 1, .commute 3, .commute
    4, .commute 5, .braid 6, .commute 3, .commute 4, .commute 0, .commute 1, .commute 2,
    .commute 3, .commute 1])
,
  ([8, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 1, 2, 0, 2], [8, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 1, 0],
    [.commute 13, .square 14])
,
  ([8, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 1, 0, 6], [8, 6, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 0],
    [.braid 9, .commute 11, .commute 12, .square 13, .commute 8])
,
  ([8, 6, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 0, 0], [8, 6, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1], [.square
    12])
,
  ([8, 6, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 6, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0,
    5, 6, 2, 1, 0, 5, 1, 2, 0], [6, 0, 8, 5, 1, 0, 5, 2, 1, 0, 6, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5,
    6, 1, 0, 5, 1, 2, 0], [.commute 10, .commute 8, .commute 9, .braid 10, .square 12, .braid 6,
    .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .braid 13, .square 15,
    .commute 10, .commute 11, .commute 12, .commute 13, .commute 9, .commute 10, .commute 5,
    .braid 6, .commute 8, .commute 4, .commute 5, .braid 6, .braid 8, .braid 10, .commute 12,
    .braid 13, .square 15, .commute 9, .commute 3, .commute 0, .braid 1, .braid 3, .commute 5,
    .commute 6, .braid 7, .braid 9, .commute 11, .commute 12, .commute 13, .square 14, .commute
    6, .commute 7, .braid 4, .commute 6, .braid 7, .commute 9, .commute 10, .commute 11,
    .commute 12, .commute 13, .commute 14, .square 15, .braid 12, .braid 14, .commute 16, .braid
    17, .commute 19, .commute 20, .commute 21, .square 22, .commute 10])
,
  ([6, 0, 8, 5, 1, 0, 5, 2, 1, 0, 6, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 1, 2, 0], [0, 1,
    2, 0, 8, 6, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 2, 0], [.commute 9, .braid 10, .commute 12,
    .commute 13, .braid 14, .commute 16, .braid 17, .commute 19, .commute 20, .square 21,
    .commute 12, .commute 8, .commute 9, .braid 10, .braid 12, .commute 14, .commute 15,
    .commute 16, .braid 17, .commute 19, .square 20, .commute 8, .commute 9, .commute 10,
    .commute 6, .commute 7, .commute 5, .commute 2, .commute 3, .commute 4, .braid 5, .braid 7,
    .commute 9, .braid 10, .commute 12, .commute 13, .commute 14, .commute 15, .commute 16,
    .braid 17, .square 19, .commute 6, .commute 2, .commute 3, .braid 4, .braid 6, .commute 8,
    .commute 9, .commute 10, .braid 11, .commute 13, .braid 14, .commute 16, .commute 17,
    .square 18, .commute 8, .commute 9, .commute 7, .commute 5, .commute 0, .commute 1, .commute
    2, .commute 3, .commute 4])
,
  ([0, 1, 2, 0, 8, 6, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 2, 0], [1, 0, 8, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 2, 1, 0, 5, 6, 0], [.braid 5, .braid 7, .braid 9, .commute 11, .braid 12, .commute 14,
    .commute 15, .commute 16, .square 17, .commute 2, .commute 3, .commute 4, .commute 5,
    .commute 6, .commute 7, .braid 0, .commute 2, .commute 3, .commute 4])
,
  ([1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 0, 0, 1, 2, 1, 0], [1, 0, 8, 5, 6, 1, 0,
    5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 2, 1, 0], [.square 17])
,
  ([1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 2, 1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2],
    [1, 0, 8, 5, 6, 5, 0, 1, 2, 5, 1, 0, 5, 8, 0, 1, 6, 5, 0, 8, 5, 6, 5, 0, 1, 2], [.braid 17,
    .commute 19, .commute 20, .square 21, .commute 20, .braid 18, .braid 20, .commute 22,
    .commute 11, .commute 12, .commute 10, .braid 8, .braid 10, .braid 12, .commute 14, .commute
    15, .commute 16, .commute 7, .commute 8, .braid 5, .commute 7, .braid 8, .commute 10,
    .commute 11, .braid 12, .commute 14, .commute 15, .braid 16, .commute 18, .commute 19,
    .braid 20, .braid 22, .square 24, .commute 14, .commute 15, .commute 16, .commute 17,
    .commute 13, .commute 14, .commute 12, .commute 11, .braid 12, .braid 14, .commute 16,
    .braid 17, .commute 19, .commute 20, .commute 7, .commute 8, .braid 9, .commute 6, .braid 7,
    .commute 9, .braid 10, .commute 12, .commute 13, .braid 14, .commute 16, .braid 17, .commute
    19, .commute 12, .braid 5, .commute 7, .commute 8])
,
  ([1, 0, 8, 5, 6, 5, 0, 1, 2, 5, 1, 0, 5, 8, 0, 1, 6, 5, 0, 8, 5, 6, 5, 0, 1, 2], [6, 1, 0, 5,
    2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 5, 0, 1, 2], [.commute 9, .braid 10,
    .braid 12, .commute 14, .commute 15, .commute 16, .braid 17, .commute 14, .commute 15,
    .commute 13, .commute 11, .braid 3, .commute 5, .commute 6, .commute 7, .commute 8, .commute
    9, .commute 10, .braid 11, .braid 13, .braid 15, .commute 17, .braid 6, .commute 8, .commute
    9, .commute 10, .commute 11, .commute 12, .commute 13, .commute 5, .braid 6, .commute 8,
    .commute 9, .commute 10, .commute 2, .commute 3, .commute 4, .commute 5, .braid 6, .commute
    1, .commute 0])
,
  ([6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 5, 0, 1, 2, 1, 0, 5, 0,
    1], [6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2,
    0, 1], [.braid 24, .commute 26, .commute 27, .commute 23, .braid 24, .commute 26, .commute
    22, .commute 23, .braid 24])
,
  ([6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0, 1,
    6, 5, 1, 0, 8, 0, 5, 6, 1], [6, 1, 0, 5, 2, 1, 0, 8, 0, 6, 5, 1, 0, 1, 2, 5, 6, 1, 0, 5, 8,
    0, 1, 2, 6, 8, 0, 5, 6, 8, 0, 5, 6, 1], [.braid 24, .commute 26, .commute 27, .commute 23,
    .braid 24, .commute 26, .braid 27, .commute 29, .commute 21, .commute 20, .braid 21,
    .commute 23, .commute 24, .commute 25, .commute 19, .commute 20, .braid 21, .commute 23,
    .commute 24, .braid 25, .commute 27, .commute 28, .braid 29, .square 31, .commute 28,
    .commute 29, .square 30, .braid 26, .commute 28, .square 29, .commute 17, .commute 18,
    .commute 19, .commute 20, .braid 15, .commute 17, .commute 18, .commute 13, .commute 12,
    .braid 13, .commute 15, .commute 16, .commute 10, .commute 11, .commute 9, .commute 10,
    .braid 11, .commute 13, .commute 14, .commute 15, .braid 16, .braid 18, .braid 20, .commute
    22, .commute 23, .commute 24, .commute 10, .commute 11, .commute 12, .braid 13, .commute 15,
    .commute 16, .commute 9, .commute 10])
,
  ([6, 1, 0, 5, 2, 1, 0, 8, 0, 6, 5, 1, 0, 1, 2, 5, 6, 1, 0, 5, 8, 0, 1, 2, 6, 8, 0, 5, 6, 8, 0,
    5, 6, 1], [6, 1, 0, 5, 2, 0, 1, 8, 0, 5, 6, 8, 2, 1, 0, 8, 5, 0, 1, 2, 6, 0, 8, 0, 5, 1, 0,
    6, 5, 1], [.braid 11, .commute 13, .commute 8, .braid 9, .commute 11, .commute 12, .braid
    13, .commute 15, .braid 16, .commute 18, .commute 19, .braid 20, .commute 22, .commute 23,
    .braid 24, .commute 26, .commute 27, .square 28, .commute 27, .braid 25, .braid 27, .square
    29, .commute 12, .commute 13, .commute 14, .braid 10, .commute 12, .commute 13, .braid 14,
    .commute 16, .commute 17, .commute 18, .commute 19, .braid 20, .commute 22, .commute 23,
    .commute 24, .commute 9, .braid 10, .commute 12, .commute 13, .braid 14, .commute 16,
    .commute 17, .braid 18, .commute 20, .commute 21, .commute 8, .commute 9, .braid 10,
    .commute 12, .commute 13, .braid 14, .braid 16, .commute 18, .commute 19, .commute 20,
    .braid 21, .commute 15, .commute 7, .braid 5, .braid 7, .commute 9, .commute 10])
,
  ([6, 1, 0, 5, 2, 0, 1, 8, 0, 5, 6, 8, 2, 1, 0, 8, 5, 0, 1, 2, 6, 0, 8, 0, 5, 1, 0, 6, 5, 1],
    [6, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 6, 5, 0, 1, 2, 0, 6, 5, 0, 8, 6, 0, 1, 5, 6, 0, 5],
    [.commute 11, .commute 12, .braid 13, .braid 15, .commute 17, .commute 18, .commute 10,
    .commute 11, .commute 12, .commute 13, .commute 9, .commute 10, .commute 8, .commute 6,
    .commute 4, .commute 5, .braid 6, .braid 8, .braid 10, .commute 12, .braid 13, .commute 15,
    .commute 16, .commute 17, .braid 18, .commute 9, .braid 2, .commute 4, .commute 5, .commute
    6, .braid 7, .braid 9, .commute 11, .commute 12, .commute 13, .braid 14, .commute 16,
    .commute 4, .commute 5, .commute 1, .braid 2, .commute 4, .braid 5, .commute 7, .commute 8,
    .braid 9, .commute 11, .braid 12, .commute 14, .commute 15, .braid 16, .commute 18, .braid
    19, .commute 21, .braid 22, .braid 24, .commute 26, .commute 27, .square 28, .commute 25,
    .commute 23, .braid 17, .commute 19, .commute 20])
,
  ([6, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 6, 5, 0, 1, 2, 0, 6, 5, 0, 8, 6, 0, 1, 5, 6, 0, 5], [6, 5,
    0, 1, 2, 1, 0, 8, 5, 0, 1, 5, 6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 1, 0], [.commute 21,
    .commute 22, .braid 23, .braid 25, .commute 22, .commute 23, .commute 16, .braid 17,
    .commute 19, .braid 20, .commute 22, .braid 23, .commute 25, .commute 15, .commute 16,
    .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .commute 14, .commute 15,
    .commute 13, .braid 11, .braid 13, .braid 15, .commute 17, .commute 10, .commute 11,
    .commute 7, .braid 8, .commute 10, .braid 11, .commute 13, .commute 14, .braid 15, .braid
    17, .commute 19, .commute 20, .braid 21, .commute 23, .commute 24, .commute 13, .braid 6,
    .commute 8, .commute 9, .commute 10, .braid 11, .braid 13, .commute 15, .commute 16, .braid
    17, .commute 19, .commute 20, .braid 21, .commute 23, .commute 9, .commute 10, .commute 11,
    .commute 8, .commute 5, .braid 6, .braid 8, .commute 10])
,
  ([6, 5, 0, 1, 2, 1, 0, 8, 5, 0, 1, 5, 6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 1, 0], [6, 5,
    2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0], [.braid 11,
    .commute 13, .commute 14, .commute 15, .commute 16, .braid 17, .commute 19, .commute 20,
    .braid 21, .commute 10, .commute 11, .braid 3, .commute 5, .commute 6, .commute 7, .commute
    8, .commute 9, .commute 10, .commute 8, .commute 2, .braid 3, .commute 5, .commute 6,
    .commute 7])
,
  ([6, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0, 0, 8,
    0], [2, 1, 5, 0, 6, 5, 1, 0, 8, 6, 2, 1, 0, 5, 6, 1, 2, 0, 5, 1, 0, 8, 0, 5, 0, 1, 2, 1, 0],
    [.square 27, .commute 26, .commute 25, .commute 24, .commute 14, .braid 12, .braid 14,
    .commute 16, .commute 17, .commute 18, .commute 19, .commute 10, .commute 9, .braid 10,
    .commute 12, .commute 13, .braid 14, .commute 16, .commute 17, .commute 12, .commute 5,
    .commute 6, .commute 7, .commute 8, .commute 9, .braid 10, .braid 12, .commute 14, .commute
    15, .commute 8, .commute 9, .commute 10, .commute 7, .commute 1, .commute 2, .braid 3,
    .commute 5, .commute 0, .commute 1, .commute 2, .braid 3, .braid 5, .braid 7, .commute 9,
    .braid 10, .commute 12, .commute 13, .commute 14, .braid 15, .braid 17, .braid 19, .commute
    21, .braid 22, .braid 20, .commute 22, .commute 19, .braid 20, .commute 18, .commute 4,
    .braid 2, .braid 4, .commute 6, .commute 7, .commute 8])
,
  ([2, 1, 5, 0, 6, 5, 1, 0, 8, 6, 2, 1, 0, 5, 6, 1, 2, 0, 5, 1, 0, 8, 0, 5, 0, 1, 2, 1, 0], [5,
    6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0],
    [.commute 9, .commute 10, .commute 11, .braid 12, .commute 14, .commute 15, .braid 16,
    .braid 18, .commute 20, .commute 15, .commute 16, .commute 5, .commute 3, .commute 1,
    .commute 2, .braid 3, .braid 5, .commute 7, .commute 8, .commute 9, .braid 10, .commute 12,
    .braid 13, .commute 15, .braid 16, .commute 18, .commute 19, .commute 12, .commute 13,
    .commute 11, .braid 9, .braid 11, .braid 13, .commute 15, .commute 16, .commute 17, .commute
    18, .commute 14, .commute 15, .commute 12, .commute 13, .commute 10, .commute 11, .commute
    8, .commute 9, .commute 10, .braid 11, .braid 13, .braid 15, .commute 17, .commute 14,
    .commute 12, .commute 13, .commute 4, .commute 0, .commute 1, .commute 2, .commute 3])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0, 1, 0,
    5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 1], [5, 6, 0, 5, 2, 1, 0, 8, 0, 2, 1, 5, 0, 5, 6, 8, 5, 0, 1,
    2, 0, 5, 1, 0, 1, 2, 0, 1], [.braid 27, .square 29, .braid 22, .commute 24, .commute 25,
    .commute 21, .braid 22, .commute 24, .braid 25, .commute 27, .square 28, .commute 24,
    .commute 25, .commute 23, .braid 21, .braid 23, .braid 25, .square 27, .square 26, .commute
    24, .square 25, .commute 17, .commute 18, .commute 19, .commute 13, .commute 14, .braid 15,
    .commute 17, .commute 18, .braid 19, .commute 21, .commute 22, .commute 23, .square 24,
    .commute 21, .commute 22, .commute 12, .braid 13, .commute 15, .commute 16, .braid 11,
    .commute 13, .commute 14, .commute 15, .braid 16, .commute 18, .braid 19, .commute 21,
    .braid 22, .square 24, .commute 17, .commute 18, .braid 19, .commute 21, .commute 16, .braid
    17, .commute 19, .commute 10, .commute 11, .commute 12, .braid 13, .commute 15, .commute 9,
    .commute 10])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 2, 1, 5, 0, 5, 6, 8, 5, 0, 1, 2, 0, 5, 1, 0, 1, 2, 0, 1], [5, 0,
    8, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 1, 0, 5, 2, 0], [.braid 11, .commute 13, .braid 6,
    .commute 8, .commute 9, .commute 7, .commute 5, .commute 4, .braid 5, .braid 7, .braid 9,
    .commute 11, .commute 12, .braid 13, .braid 15, .commute 17, .commute 18, .braid 19, .braid
    21, .square 23, .commute 18, .commute 19, .braid 16, .commute 18, .braid 19, .commute 21,
    .square 22, .square 21, .square 20, .commute 15, .braid 16, .commute 18, .commute 12,
    .commute 13, .braid 10, .commute 12, .commute 9, .braid 10, .commute 8, .commute 3, .commute
    4, .commute 5, .braid 6, .braid 8, .commute 10, .commute 5, .commute 6, .commute 1, .commute
    2])
,
  ([5, 0, 8, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 1, 0, 5, 2, 0, 1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2,
    0, 1], [5, 0, 8, 6, 1, 2, 5, 0, 1, 8, 0, 5, 2, 8, 6, 0, 1, 5, 0, 8, 2, 1, 0, 5, 0, 1, 2, 1,
    0], [.commute 17, .commute 16, .braid 17, .commute 19, .braid 20, .commute 22, .braid 18,
    .commute 20, .commute 16, .commute 15, .braid 16, .commute 18, .commute 19, .braid 20,
    .braid 22, .square 24, .commute 21, .commute 15, .commute 16, .braid 17, .braid 19, .braid
    21, .commute 23, .commute 24, .commute 25, .braid 26, .commute 18, .braid 16, .braid 18,
    .commute 20, .commute 21, .commute 22, .braid 23, .commute 21, .commute 19, .commute 10,
    .braid 8, .braid 10, .commute 12, .commute 13, .commute 14, .commute 6, .commute 5, .braid
    6, .commute 8, .commute 9, .braid 10, .commute 12, .commute 13, .braid 14, .commute 16,
    .commute 17, .commute 18, .braid 19, .braid 21, .commute 23, .braid 24, .commute 26, .braid
    27, .square 29, .commute 18, .commute 19, .commute 12, .commute 13])
,
  ([5, 0, 8, 6, 1, 2, 5, 0, 1, 8, 0, 5, 2, 8, 6, 0, 1, 5, 0, 8, 2, 1, 0, 5, 0, 1, 2, 1, 0], [5,
    6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0],
    [.commute 14, .commute 15, .commute 11, .commute 12, .commute 10, .commute 9, .braid 10,
    .braid 12, .commute 14, .braid 15, .commute 17, .commute 18, .commute 5, .commute 6, .braid
    7, .commute 4, .braid 5, .commute 7, .braid 8, .commute 10, .commute 11, .braid 12, .commute
    14, .braid 15, .commute 17, .commute 13, .commute 14, .braid 6, .commute 8, .commute 9,
    .commute 10, .commute 11, .commute 12, .commute 13, .commute 11, .commute 5, .braid 6,
    .commute 8, .commute 9, .commute 10, .commute 2, .commute 3, .commute 4, .commute 5, .braid
    6, .commute 1])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0, 2, 1,
    0, 8, 0, 1, 2], [5, 6, 0, 5, 2, 1, 0, 8, 2, 1, 5, 0, 1, 5, 6, 5, 0, 8, 2, 1, 0, 5, 1, 2, 1,
    0], [.braid 25, .commute 27, .square 28, .commute 24, .braid 25, .square 27, .square 26,
    .commute 17, .commute 18, .commute 19, .commute 20, .commute 13, .commute 14, .braid 15,
    .commute 17, .commute 18, .commute 12, .braid 13, .commute 15, .commute 16, .braid 11,
    .commute 13, .commute 14, .commute 15, .braid 16, .braid 18, .braid 20, .commute 22,
    .commute 23, .commute 24, .square 25, .commute 10, .commute 11, .commute 12, .braid 13,
    .commute 15, .commute 16, .commute 9, .commute 10, .braid 11, .commute 13, .commute 8,
    .braid 9, .commute 11, .commute 12, .braid 13, .commute 15, .braid 16, .commute 18, .commute
    19, .braid 20, .commute 22, .braid 23, .square 25, .commute 24, .braid 22, .commute 18,
    .commute 15, .commute 16, .commute 17, .commute 12, .commute 13, .braid 10, .commute 12])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 2, 1, 5, 0, 1, 5, 6, 5, 0, 8, 2, 1, 0, 5, 1, 2, 1, 0], [5, 2, 1, 0,
    8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 1, 0], [.braid 13, .commute 15,
    .commute 16, .commute 9, .braid 10, .commute 12, .braid 13, .commute 15, .commute 7,
    .commute 8, .commute 6, .commute 3, .commute 4, .commute 5, .braid 6, .braid 8, .commute 10,
    .commute 11, .commute 12, .braid 13, .commute 10, .commute 11, .commute 9, .commute 7,
    .commute 1, .commute 2, .commute 3, .commute 4, .commute 5, .commute 6, .braid 7, .braid 9,
    .braid 11, .commute 13, .commute 4, .commute 5, .commute 6, .commute 7, .commute 8, .commute
    9, .commute 1, .braid 2, .commute 4, .commute 5, .commute 6])
,
  ([5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 1, 0, 2, 1, 0, 8, 0,
    1, 2], [5, 2, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5, 0, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 0, 1, 2, 1,
    0], [.braid 22, .commute 24, .square 25, .braid 23, .square 25, .commute 24, .braid 25,
    .commute 27, .commute 22, .commute 23, .commute 24, .braid 25, .braid 20, .commute 22,
    .commute 13, .braid 11, .braid 13, .commute 15, .commute 16, .commute 17, .commute 18,
    .commute 19, .braid 20, .commute 18, .commute 9, .commute 8, .braid 9, .commute 11, .commute
    12, .braid 13, .commute 15, .commute 16, .commute 6, .commute 7, .commute 5, .commute 6,
    .braid 7, .commute 9, .commute 10, .commute 11, .commute 12, .braid 13, .commute 15, .braid
    16, .braid 18, .commute 20, .commute 15, .commute 16, .commute 10, .commute 4, .commute 5,
    .commute 6, .commute 7, .braid 8, .braid 10, .commute 12, .commute 13, .braid 2, .commute 4,
    .commute 5, .braid 6, .commute 8, .commute 9, .braid 10])
,
  ([5, 2, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5, 0, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 0, 1, 2, 1, 0], [5,
    6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0],
    [.commute 12, .braid 13, .commute 15, .braid 16, .commute 18, .commute 19, .commute 12,
    .commute 13, .commute 11, .braid 9, .braid 11, .braid 13, .commute 15, .commute 16, .commute
    17, .commute 18, .commute 14, .commute 15, .commute 12, .commute 13, .commute 10, .commute
    11, .commute 4, .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10,
    .braid 11, .braid 13, .braid 15, .commute 17, .commute 14, .commute 12, .commute 13,
    .commute 3, .commute 4, .commute 1, .commute 2, .commute 3, .commute 1])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0, 1, 2,
    1], [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 2, 1, 0, 5, 1, 2, 1, 0],
    [.braid 25, .commute 27, .commute 24, .braid 25, .braid 27, .square 29, .square 28, .commute
    26, .braid 24])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 2, 1, 0, 5, 1, 2, 1, 0, 1, 2,
    1], [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0],
    [.braid 24, .commute 26, .braid 27, .square 29, .braid 25, .commute 27, .commute 24, .braid
    25])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0, 6],
    [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1, 0],
    [.commute 28, .commute 27, .commute 26, .commute 25, .commute 24, .commute 19, .commute 20,
    .commute 21, .braid 22, .commute 18, .commute 19, .braid 20, .commute 22])
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
