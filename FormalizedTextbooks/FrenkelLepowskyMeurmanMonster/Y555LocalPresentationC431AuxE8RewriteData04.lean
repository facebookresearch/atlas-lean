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
/-- Exact bounded chunks of literal E8 square, commutation and braid moves, block 4. -/
def y431AuxE8RewriteData04 : Fin 64 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
![
  ([5, 6, 8, 2, 1, 0, 8, 5, 0, 1, 2, 0, 5, 6, 8, 0, 5, 1, 0, 8, 6, 5, 0, 1, 5, 0, 1, 2, 1], [5,
    6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 5, 1, 2, 0, 1, 0], [.commute 2,
    .commute 3, .braid 4, .braid 6, .commute 8, .commute 9, .braid 10, .commute 12, .braid 13,
    .commute 15, .commute 16, .braid 17, .commute 19, .braid 20, .commute 22, .square 23, .braid
    21, .square 23, .commute 22, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13,
    .commute 14, .braid 7, .commute 9, .commute 10, .commute 11, .commute 6, .braid 7, .commute
    9, .commute 5, .braid 3, .braid 5, .commute 7, .commute 8, .braid 9, .braid 11, .commute 13,
    .braid 14, .commute 16, .commute 17, .commute 18, .commute 19, .braid 20, .braid 22,
    .commute 8, .commute 9, .braid 6, .commute 8, .commute 5, .braid 6, .commute 4, .commute 2,
    .commute 3])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 5, 1, 2, 0, 1, 0, 1], [5, 6, 0, 5,
    2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 5, 1, 2, 1, 0], [.braid 22, .square 24])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 5, 1, 2, 1, 0, 8], [5, 6, 2, 5, 0,
    1, 8, 0, 5, 6, 2, 8, 0, 1, 8, 5, 0, 8, 5, 1, 2, 1, 0], [.commute 17, .commute 18, .commute
    19, .commute 20, .commute 21, .commute 16, .commute 13, .commute 14, .commute 10, .commute
    11, .commute 12, .commute 13, .braid 14, .braid 16, .commute 13, .commute 14, .commute 11,
    .commute 9, .commute 10, .braid 11, .commute 13, .braid 14, .commute 16, .braid 17, .commute
    19, .commute 10, .commute 11, .commute 12, .braid 8, .commute 10, .commute 11, .braid 12,
    .commute 14, .commute 15, .commute 16, .braid 17, .braid 19, .braid 21, .square 23, .commute
    20, .commute 18, .commute 19, .braid 16, .commute 18, .commute 15, .braid 13, .braid 15,
    .commute 17, .commute 7, .braid 5, .braid 7, .commute 9, .commute 10, .commute 11, .commute
    3, .commute 2, .braid 3, .commute 5, .commute 6, .braid 7, .commute 9, .commute 10, .braid
    11, .commute 13])
,
  ([5, 6, 2, 5, 0, 1, 8, 0, 5, 6, 2, 8, 0, 1, 8, 5, 0, 8, 5, 1, 2, 1, 0], [6, 5, 2, 1, 0, 8, 5,
    6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 1, 2, 1, 0], [.commute 14, .braid 15, .commute 13,
    .commute 1, .commute 0, .braid 1, .commute 3, .commute 4, .commute 5, .commute 6, .braid 7,
    .commute 9, .commute 10, .braid 11, .braid 13, .commute 15, .commute 8, .commute 9, .commute
    10, .commute 7, .commute 8, .commute 6, .commute 5, .braid 6, .braid 8, .braid 10, .commute
    12, .commute 13, .commute 14, .commute 5, .commute 6, .commute 7, .commute 8, .commute 9,
    .commute 10, .commute 8, .braid 3, .commute 5, .commute 6, .commute 7, .commute 0, .commute
    1])
,
  ([6, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 1, 2, 1, 0, 2], [6, 5, 2, 1, 0, 8,
    5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 1, 0], [.braid 19, .commute 21, .square 22])
,
  ([6, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 1, 0, 0], [6, 5, 2, 1, 0, 8, 5,
    6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 1], [.square 21])
,
  ([6, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 1, 5], [6, 5, 2, 1, 0, 8, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 6, 1, 2, 0, 1], [.commute 18, .commute 19, .square 20, .commute 17])
,
  ([6, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 2, 0, 1, 1], [6, 5, 2, 1, 0, 8, 5, 6, 1,
    0, 5, 2, 1, 0, 8, 6, 1, 2, 0], [.square 19])
,
  ([6, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 2, 0, 8], [5, 6, 0, 5, 2, 1, 0, 8, 1, 0,
    5, 6, 0, 5, 1, 2, 1, 0], [.commute 14, .commute 15, .commute 16, .commute 13, .commute 12,
    .braid 13, .commute 15, .braid 16, .square 18, .commute 11, .commute 12, .braid 13, .commute
    15, .commute 14, .commute 13, .commute 7, .commute 8, .braid 9, .commute 6, .braid 7,
    .commute 9, .braid 10, .commute 12, .commute 5, .braid 3, .braid 5, .commute 7, .commute 8,
    .commute 9, .braid 10, .braid 7, .commute 9, .commute 10, .commute 6, .braid 7, .commute 9,
    .commute 5, .commute 6, .braid 7, .commute 4, .commute 5, .commute 3, .commute 1, .commute
    0, .braid 1, .braid 3, .braid 5, .commute 7, .commute 0, .commute 1, .commute 2, .commute
    3])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 1, 2, 1, 0, 6], [5, 6, 0, 5, 2, 1, 0, 8, 5, 6, 1,
    0, 5, 1, 2, 1, 0], [.commute 11, .braid 9, .braid 11, .commute 13, .commute 14, .commute 15,
    .commute 16, .square 17, .commute 10, .commute 8, .commute 9])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 1, 2, 1, 0, 2], [5, 6, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0,
    5, 2, 1, 0], [.braid 13, .commute 15, .square 16])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 0], [5, 6, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5,
    2, 1], [.square 15])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 5], [5, 6, 0, 5, 2, 1, 0, 8, 5, 6, 1, 2, 0, 1],
    [.commute 12, .commute 13, .square 14, .commute 11])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 5, 6, 1, 2, 0, 1, 1], [5, 6, 0, 5, 2, 1, 0, 8, 5, 6, 1, 2, 0],
    [.square 13])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 5, 6, 1, 2, 0, 8], [6, 5, 2, 1, 0, 8, 5, 6, 5, 1, 2, 0], [.commute
    7, .commute 8, .commute 9, .commute 10, .commute 3, .commute 4, .braid 5, .commute 7,
    .commute 2, .braid 3, .commute 5, .commute 6, .braid 7, .commute 9, .braid 10, .square 12,
    .commute 9, .commute 8, .commute 1, .commute 2, .commute 3, .braid 4, .commute 0, .commute
    1, .braid 2, .commute 4, .braid 5, .commute 7, .braid 3, .commute 5, .commute 6, .commute 2,
    .braid 3, .commute 5, .commute 1, .commute 2, .commute 0, .commute 1])
,
  ([6, 5, 2, 1, 0, 8, 5, 6, 5, 1, 2, 0, 2], [6, 5, 2, 1, 0, 8, 5, 6, 5, 1, 0], [.commute 10,
    .square 11])
,
  ([6, 5, 2, 1, 0, 8, 5, 6, 5, 1, 0, 6], [6, 5, 2, 1, 0, 8, 6, 5, 1, 0], [.braid 6, .commute 8,
    .commute 9, .square 10])
,
  ([6, 5, 2, 1, 0, 8, 6, 5, 1, 0, 0], [6, 5, 2, 1, 0, 8, 6, 5, 1], [.square 9])
,
  ([6, 5, 2, 1, 0, 8, 6, 5, 1, 6, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2,
    1, 0, 5, 1, 2, 0], [6, 1, 0, 2, 5, 6, 1, 2, 0, 1, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5,
    1, 2, 0], [.commute 7, .commute 6, .braid 7, .square 9, .commute 5, .commute 6, .commute 7,
    .commute 8, .commute 9, .braid 10, .square 12, .commute 7, .commute 8, .commute 9, .commute
    10, .commute 6, .commute 7, .braid 3, .commute 5, .commute 2, .braid 3, .braid 5, .braid 7,
    .commute 9, .braid 10, .square 12, .commute 4, .braid 2, .braid 4, .commute 6, .commute 7,
    .commute 8, .commute 9, .commute 10, .commute 5, .commute 3, .commute 1, .commute 2, .braid
    3, .braid 5, .commute 7, .commute 8, .commute 9, .braid 10, .commute 12, .commute 13,
    .square 14, .commute 9, .commute 10, .braid 11, .braid 13, .commute 15, .braid 16, .commute
    18, .commute 19, .commute 20, .square 21, .commute 7, .commute 8, .commute 9, .commute 6,
    .commute 7, .commute 5, .commute 2])
,
  ([6, 1, 0, 2, 5, 6, 1, 2, 0, 1, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 1, 2, 0], [1, 0, 8,
    5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 5, 0], [.commute 3, .commute 4, .braid 5, .braid
    7, .braid 9, .commute 11, .commute 12, .braid 13, .commute 15, .braid 16, .commute 18,
    .commute 19, .square 20, .commute 11, .commute 8, .braid 9, .braid 11, .commute 13, .commute
    14, .commute 15, .braid 16, .commute 18, .square 19, .braid 7, .commute 9, .commute 10,
    .braid 11, .commute 13, .braid 14, .commute 16, .commute 17, .commute 18, .square 19,
    .commute 9, .commute 0, .commute 1, .braid 2, .commute 4, .commute 5, .commute 6, .braid 7,
    .braid 9, .commute 11, .braid 12, .commute 14, .commute 15, .commute 16, .commute 17,
    .square 18, .commute 5, .commute 6, .commute 7, .commute 4, .commute 3, .commute 2])
,
  ([1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 5, 0, 0, 1, 2, 1, 0], [1, 0, 8, 5, 6, 1,
    0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 5, 1, 2, 1, 0], [.square 18])
,
  ([1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 5, 1, 2, 1, 0, 5, 2, 1, 0, 8, 0, 5, 1,
    2], [1, 0, 8, 5, 6, 0, 5, 0, 1, 2, 1, 0, 8, 1, 5, 6, 0, 1, 5, 0, 8, 6, 1, 0, 5, 0, 1, 2, 0],
    [.braid 18, .commute 20, .commute 21, .square 22, .commute 21, .braid 19, .braid 21,
    .commute 23, .braid 24, .commute 20, .commute 17, .braid 18, .braid 20, .commute 22,
    .commute 11, .commute 12, .commute 10, .braid 8, .braid 10, .braid 12, .commute 14, .commute
    15, .commute 16, .commute 7, .commute 8, .braid 5, .commute 7, .braid 8, .commute 10,
    .commute 11, .braid 12, .commute 14, .commute 15, .braid 16, .commute 18, .commute 19,
    .braid 20, .braid 22, .commute 24, .braid 25, .commute 27, .commute 14, .commute 15,
    .commute 16, .commute 13, .commute 14, .commute 12, .commute 11, .braid 12, .braid 14,
    .braid 16, .commute 18, .commute 19, .commute 20, .commute 17, .commute 15, .commute 7,
    .commute 8, .braid 9, .commute 6, .braid 7, .commute 9, .braid 10, .commute 12])
,
  ([1, 0, 8, 5, 6, 0, 5, 0, 1, 2, 1, 0, 8, 1, 5, 6, 0, 1, 5, 0, 8, 6, 1, 0, 5, 0, 1, 2, 0], [6,
    1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 0],
    [.commute 13, .commute 14, .braid 15, .braid 17, .commute 19, .commute 12, .commute 13,
    .braid 5, .commute 7, .commute 8, .commute 9, .braid 10, .commute 12, .braid 13, .commute
    15, .commute 16, .braid 17, .commute 15, .braid 3, .commute 5, .commute 6, .commute 7,
    .commute 8, .commute 9, .braid 10, .commute 12, .braid 13, .braid 15, .commute 17, .braid 6,
    .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .commute 5,
    .braid 6, .commute 8, .commute 9, .commute 10, .commute 9, .commute 8, .commute 2, .commute
    3, .commute 4, .commute 5, .braid 6, .commute 1, .commute 0])
,
  ([6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 0, 1, 0,
    5, 0, 1], [6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0,
    1, 2, 0], [.braid 23, .commute 25, .commute 26, .commute 22, .braid 23, .commute 25, .braid
    26, .commute 28, .braid 29, .square 31, .braid 27, .commute 29, .square 30, .commute 26,
    .braid 27, .braid 24, .commute 26, .commute 27, .commute 23, .braid 24, .commute 26,
    .commute 22, .commute 23, .braid 24])
,
  ([6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0, 6,
    5, 1, 0, 8, 0, 5, 6, 1], [6, 1, 0, 5, 2, 1, 0, 8, 0, 1, 2, 0, 5, 6, 1, 0, 5, 1, 8, 0, 1, 2,
    6, 1, 8, 0, 5, 6, 0, 1, 8, 0, 5, 6, 1], [.braid 24, .commute 26, .commute 27, .commute 23,
    .braid 24, .commute 26, .braid 27, .commute 21, .commute 20, .braid 21, .commute 23,
    .commute 24, .commute 25, .commute 19, .commute 20, .braid 21, .commute 23, .commute 24,
    .braid 25, .commute 27, .braid 28, .square 30, .braid 26, .commute 28, .commute 19, .commute
    20, .commute 21, .braid 22, .commute 24, .commute 18, .commute 19, .braid 20, .commute 22,
    .commute 23, .braid 24, .commute 26, .commute 27, .braid 28, .square 30, .commute 17,
    .commute 18, .commute 16, .commute 13, .commute 14, .commute 10, .commute 11, .commute 12,
    .commute 13, .braid 14, .braid 16, .braid 18, .commute 20, .commute 21, .commute 22,
    .commute 23, .commute 13, .commute 14, .commute 11, .commute 9, .commute 10, .braid 11,
    .commute 13, .braid 14, .commute 16])
,
  ([6, 1, 0, 5, 2, 1, 0, 8, 0, 1, 2, 0, 5, 6, 1, 0, 5, 1, 8, 0, 1, 2, 6, 1, 8, 0, 5, 6, 0, 1, 8,
    0, 5, 6, 1], [6, 1, 5, 0, 8, 1, 2, 0, 5, 1, 0, 8, 6, 5, 0, 1, 2, 0, 5, 6, 5, 0, 1, 8, 0, 5,
    6, 8, 0, 1, 8, 0, 5, 6, 1], [.commute 17, .braid 18, .commute 20, .commute 21, .commute 10,
    .commute 11, .commute 12, .braid 8, .commute 10, .commute 11, .braid 12, .commute 14,
    .commute 15, .commute 16, .commute 17, .braid 18, .commute 20, .braid 21, .braid 23,
    .commute 25, .commute 26, .commute 15, .commute 7, .braid 5, .braid 7, .commute 9, .commute
    10, .commute 11, .commute 12, .braid 13, .braid 15, .commute 17, .commute 18, .commute 10,
    .commute 11, .commute 12, .commute 13, .commute 9, .commute 10, .commute 8, .commute 6,
    .commute 4, .commute 5, .braid 6, .braid 8, .braid 10, .commute 12, .braid 13, .commute 15,
    .commute 16, .commute 17, .braid 18, .commute 9, .braid 2, .commute 4, .commute 5, .commute
    6, .braid 7, .braid 9, .commute 11, .commute 12, .commute 13, .braid 14, .commute 16])
,
  ([6, 1, 5, 0, 8, 1, 2, 0, 5, 1, 0, 8, 6, 5, 0, 1, 2, 0, 5, 6, 5, 0, 1, 8, 0, 5, 6, 8, 0, 1, 8,
    0, 5, 6, 1], [6, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 6, 5, 1, 0, 6, 5, 2, 1, 0, 8, 0, 2, 1, 5, 6,
    0, 5, 0], [.commute 4, .commute 5, .commute 1, .braid 2, .commute 4, .braid 5, .commute 7,
    .commute 8, .braid 9, .commute 11, .braid 12, .commute 14, .commute 15, .braid 16, .commute
    18, .braid 19, .commute 21, .commute 22, .braid 23, .commute 25, .braid 26, .commute 28,
    .square 29, .commute 25, .commute 26, .commute 27, .commute 28, .commute 24, .braid 22,
    .braid 24, .commute 26, .braid 20, .commute 22, .commute 23, .braid 24, .braid 26, .braid
    28, .square 30, .commute 25, .braid 23, .braid 25, .commute 27, .commute 28, .square 29,
    .commute 26, .commute 24, .braid 17, .commute 19, .commute 20, .commute 21, .commute 22,
    .commute 23, .braid 24, .braid 26, .commute 15, .commute 16, .commute 17, .braid 13,
    .commute 15, .commute 16, .braid 17, .commute 19, .commute 20, .commute 21])
,
  ([6, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 6, 5, 1, 0, 6, 5, 2, 1, 0, 8, 0, 2, 1, 5, 6, 0, 5, 0], [6,
    5, 0, 8, 5, 2, 1, 0, 8, 1, 2, 5, 0, 1, 6, 5, 0, 8, 1, 2, 0, 5, 6, 1, 0, 5, 1, 2, 0],
    [.commute 14, .commute 12, .commute 11, .braid 12, .braid 14, .commute 16, .braid 17,
    .commute 19, .commute 10, .commute 11, .commute 12, .braid 8, .braid 6, .commute 8, .braid
    9, .commute 11, .braid 12, .commute 14, .commute 15, .commute 16, .braid 17, .braid 19,
    .braid 21, .commute 23, .commute 24, .commute 25, .commute 26, .commute 22, .commute 23,
    .commute 20, .commute 14, .commute 15, .commute 13, .braid 7, .commute 9, .commute 10,
    .commute 11, .commute 4, .commute 5, .commute 3, .commute 4, .braid 5, .commute 7, .commute
    8, .commute 9, .commute 10, .braid 11, .braid 13, .braid 15, .commute 17, .commute 18,
    .commute 19, .braid 20, .commute 22, .braid 23, .commute 25, .commute 9, .commute 10,
    .commute 11, .commute 12, .commute 13, .commute 8, .commute 9, .commute 10])
,
  ([6, 5, 0, 8, 5, 2, 1, 0, 8, 1, 2, 5, 0, 1, 6, 5, 0, 8, 1, 2, 0, 5, 6, 1, 0, 5, 1, 2, 0], [6,
    0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [.commute 3, .commute 4, .commute 5, .braid 6, .braid 1, .commute 3, .braid 4, .commute 6,
    .braid 7, .commute 9, .braid 10, .commute 12, .braid 13, .commute 15, .commute 16, .commute
    17, .commute 18, .commute 19, .braid 20, .commute 22, .braid 23, .commute 18, .commute 19,
    .commute 20, .commute 12, .commute 13, .commute 9, .commute 10, .commute 11, .commute 12,
    .commute 10, .commute 8, .commute 9])
,
  ([6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0, 0, 8,
    0], [0, 2, 1, 8, 5, 0, 6, 5, 6, 1, 0, 8, 2, 1, 0, 5, 6, 1, 2, 0, 5, 1, 0, 8, 0, 5, 0, 1, 2,
    0], [.square 28, .commute 27, .commute 26, .commute 16, .braid 14, .braid 16, .commute 18,
    .commute 19, .commute 20, .commute 21, .commute 12, .commute 11, .braid 12, .commute 14,
    .commute 15, .braid 16, .commute 18, .commute 19, .commute 14, .braid 5, .commute 7,
    .commute 8, .commute 9, .commute 10, .commute 11, .braid 12, .braid 14, .commute 16,
    .commute 17, .commute 10, .commute 11, .commute 12, .commute 9, .commute 2, .commute 3,
    .commute 4, .braid 5, .commute 7, .commute 0, .commute 1, .commute 2, .commute 3, .commute
    4, .braid 5, .braid 7, .braid 9, .commute 11, .braid 12, .commute 14, .commute 15, .commute
    16, .braid 17, .braid 19, .braid 21, .commute 23, .braid 24, .braid 22, .commute 24,
    .commute 21, .braid 22, .commute 20, .commute 6, .braid 4, .braid 6])
,
  ([0, 2, 1, 8, 5, 0, 6, 5, 6, 1, 0, 8, 2, 1, 0, 5, 6, 1, 2, 0, 5, 1, 0, 8, 0, 5, 0, 1, 2, 0],
    [0, 2, 5, 8, 6, 0, 8, 1, 0, 5, 6, 0, 1, 2, 8, 0, 1, 5, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [.commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .braid 14,
    .commute 16, .commute 17, .braid 18, .braid 20, .commute 22, .commute 17, .commute 18,
    .commute 7, .commute 5, .commute 2, .commute 3, .commute 4, .braid 5, .braid 7, .commute 9,
    .commute 10, .commute 11, .braid 12, .commute 14, .braid 15, .commute 17, .braid 18,
    .commute 20, .commute 21, .commute 14, .commute 15, .commute 13, .braid 11, .braid 13,
    .braid 15, .commute 17, .commute 18, .commute 19, .commute 20, .commute 16, .commute 17,
    .commute 14, .commute 15, .commute 12, .commute 13, .commute 10, .commute 11, .commute 12,
    .braid 13, .braid 15, .braid 17, .commute 19, .braid 8, .commute 10, .commute 11, .commute
    12, .commute 13, .commute 7, .braid 8, .commute 10, .commute 6, .commute 2])
,
  ([0, 2, 5, 8, 6, 0, 8, 1, 0, 5, 6, 0, 1, 2, 8, 0, 1, 5, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [.commute 3, .braid 4, .braid 6, .commute 8, .commute 9, .braid 10, .commute 12, .braid 13,
    .commute 15, .commute 16, .braid 17, .commute 15, .commute 3, .commute 4, .commute 5,
    .commute 6, .braid 7, .commute 0, .braid 1, .commute 3, .commute 4, .braid 5, .commute 7,
    .braid 8, .commute 10, .commute 11, .commute 12, .braid 13, .braid 15, .commute 17, .commute
    11, .commute 12, .commute 13, .commute 10, .braid 6, .commute 8, .commute 9, .commute 5,
    .braid 6, .commute 8, .commute 3, .commute 4, .commute 5, .braid 6, .commute 3, .commute 4,
    .commute 0, .commute 1, .commute 2, .commute 3, .commute 1])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0, 1,
    0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 1], [5, 6, 0, 5, 2, 1, 8, 0, 5, 6, 1, 2, 5, 0, 8, 1, 0, 5,
    6, 8, 0, 1, 2, 8, 0, 5, 1, 8, 8, 0, 5, 1, 2, 0, 1], [.braid 24, .commute 26, .commute 27,
    .commute 23, .braid 24, .commute 26, .braid 27, .commute 29, .commute 22, .commute 23,
    .braid 24, .commute 26, .braid 27, .braid 29, .square 31, .commute 25, .commute 26, .commute
    24, .braid 22, .braid 24, .braid 26, .commute 28, .commute 29, .square 30, .commute 27,
    .commute 25, .commute 23, .commute 24, .braid 25, .braid 27, .square 29, .square 28,
    .commute 17, .braid 15, .braid 17, .commute 19, .commute 20, .commute 13, .commute 12,
    .braid 13, .commute 15, .commute 16, .braid 17, .commute 19, .braid 20, .commute 22,
    .commute 23, .commute 15, .braid 6, .commute 8, .commute 9, .commute 10, .commute 11,
    .commute 12, .braid 13, .braid 15, .commute 17, .commute 18, .commute 19, .braid 20,
    .commute 22, .braid 23, .commute 25, .commute 26])
,
  ([5, 6, 0, 5, 2, 1, 8, 0, 5, 6, 1, 2, 5, 0, 8, 1, 0, 5, 6, 8, 0, 1, 2, 8, 0, 5, 1, 8, 8, 0, 5,
    1, 2, 0, 1], [5, 0, 8, 5, 6, 0, 5, 2, 1, 2, 0, 1, 8, 0, 5, 6, 0, 8, 5, 0, 1, 2, 8, 0, 5, 1,
    0, 1, 2, 0, 1], [.square 27, .commute 25, .commute 11, .commute 12, .commute 13, .commute
    10, .commute 3, .commute 4, .commute 5, .braid 6, .commute 8, .commute 1, .commute 2,
    .commute 3, .commute 4, .commute 5, .braid 6, .braid 8, .braid 10, .commute 12, .braid 13,
    .commute 15, .commute 16, .commute 17, .commute 18, .commute 19, .braid 20, .commute 22,
    .braid 23, .braid 25, .square 27, .commute 24, .commute 7, .braid 5, .braid 7, .commute 9,
    .commute 10, .commute 11, .commute 12, .commute 13, .commute 14, .braid 15, .commute 17,
    .commute 8, .commute 6, .commute 3, .commute 4, .commute 5, .braid 6, .braid 8, .commute 10,
    .commute 11, .commute 12, .braid 13, .commute 15, .commute 10, .commute 11, .commute 9,
    .commute 7, .commute 2, .commute 3, .commute 4, .commute 5, .commute 6])
,
  ([5, 0, 8, 5, 6, 0, 5, 2, 1, 2, 0, 1, 8, 0, 5, 6, 0, 8, 5, 0, 1, 2, 8, 0, 5, 1, 0, 1, 2, 0,
    1], [5, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 2, 8, 1, 0, 5, 6, 1, 0, 5, 2, 0], [.braid 7, .braid
    9, .braid 11, .commute 13, .commute 14, .braid 15, .braid 17, .commute 19, .commute 20,
    .commute 21, .braid 22, .braid 24, .square 26, .commute 20, .commute 21, .commute 22,
    .commute 19, .commute 16, .braid 17, .braid 19, .commute 21, .braid 22, .commute 24, .square
    25, .square 24, .square 23, .braid 15, .commute 17, .commute 18, .braid 19, .commute 21,
    .braid 13, .commute 15, .commute 16, .commute 12, .braid 13, .commute 15, .commute 11,
    .commute 12, .braid 13, .commute 10, .commute 11, .commute 9, .commute 6, .commute 7,
    .commute 4, .commute 5, .commute 6, .braid 7, .braid 9, .braid 11, .commute 13, .commute 6,
    .commute 7, .commute 8, .commute 9, .commute 5, .commute 6, .braid 3, .commute 5, .braid 6,
    .commute 8, .braid 9, .commute 11])
,
  ([5, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 2, 8, 1, 0, 5, 6, 1, 0, 5, 2, 0], [5, 0, 8, 0, 5, 6, 1,
    0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 2, 0], [.commute 12])
,
  ([5, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 2, 0, 1, 0, 5, 2, 1, 0, 8, 0,
    5, 1, 2, 0, 1], [5, 0, 8, 5, 0, 1, 2, 6, 5, 0, 1, 8, 0, 5, 6, 0, 5, 2, 8, 0, 1, 2, 5, 0, 8,
    1, 0, 1, 5, 0, 1, 2, 0, 1], [.commute 20, .commute 19, .braid 20, .commute 22, .braid 23,
    .commute 25, .braid 21, .commute 23, .commute 19, .commute 18, .braid 19, .commute 21,
    .commute 22, .braid 23, .braid 25, .square 27, .commute 22, .commute 23, .braid 20, .commute
    22, .braid 23, .commute 25, .commute 26, .braid 27, .commute 25, .commute 12, .commute 13,
    .commute 11, .braid 9, .braid 11, .braid 13, .commute 15, .commute 16, .commute 17, .commute
    18, .commute 8, .commute 9, .braid 6, .commute 8, .braid 9, .commute 11, .commute 12, .braid
    13, .commute 15, .commute 5, .commute 6, .commute 7, .braid 3, .commute 5, .commute 6,
    .braid 7, .commute 9, .commute 10, .commute 11, .commute 12, .braid 13, .braid 15, .commute
    17, .braid 18, .commute 20, .commute 21, .commute 22, .braid 23, .braid 25])
,
  ([5, 0, 8, 5, 0, 1, 2, 6, 5, 0, 1, 8, 0, 5, 6, 0, 5, 2, 8, 0, 1, 2, 5, 0, 8, 1, 0, 1, 5, 0, 1,
    2, 0, 1], [5, 0, 8, 5, 6, 5, 0, 1, 5, 2, 1, 0, 5, 6, 8, 0, 1, 5, 0, 8, 5, 6, 2, 1, 0, 5, 0,
    1, 2, 0], [.commute 27, .braid 28, .commute 30, .square 31, .commute 21, .commute 22,
    .commute 23, .commute 20, .commute 16, .commute 17, .braid 18, .braid 20, .commute 22,
    .braid 23, .commute 25, .commute 26, .commute 27, .braid 28, .square 30, .commute 15, .braid
    16, .commute 18, .commute 19, .braid 20, .commute 22, .braid 23, .commute 25, .braid 26,
    .commute 28, .commute 14, .commute 15, .commute 16, .commute 13, .commute 14, .commute 12,
    .commute 11, .braid 12, .braid 14, .braid 16, .commute 18, .commute 19, .commute 20,
    .commute 17, .commute 15, .commute 6, .commute 7, .commute 8, .braid 9, .commute 5, .commute
    6, .braid 7, .commute 9, .braid 10, .commute 12, .commute 13, .commute 14, .braid 15, .braid
    17, .commute 19, .commute 12, .commute 13, .commute 4, .braid 5, .commute 7])
,
  ([5, 0, 8, 5, 6, 5, 0, 1, 5, 2, 1, 0, 5, 6, 8, 0, 1, 5, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [.commute 8, .commute 9, .braid 10, .commute 12, .braid 13, .commute 15, .commute 16, .braid
    17, .commute 15, .braid 3, .commute 5, .commute 6, .commute 7, .commute 8, .commute 9,
    .braid 10, .commute 12, .braid 13, .braid 15, .commute 17, .braid 6, .commute 8, .commute 9,
    .commute 10, .commute 11, .commute 12, .commute 13, .commute 5, .braid 6, .commute 8,
    .commute 9, .commute 10, .commute 9, .commute 8, .commute 2, .commute 3, .commute 4,
    .commute 5, .braid 6, .commute 1])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0, 2,
    1, 0, 8, 0, 1, 2], [5, 0, 2, 1, 8, 5, 0, 6, 5, 1, 0, 6, 8, 2, 1, 0, 5, 6, 1, 2, 0, 1, 8, 0,
    5, 1, 0, 1, 2], [.commute 28, .square 29, .braid 26, .square 28, .square 27, .commute 17,
    .braid 15, .braid 17, .commute 19, .commute 20, .commute 21, .commute 22, .commute 13,
    .commute 12, .braid 13, .commute 15, .commute 16, .braid 17, .commute 19, .commute 20,
    .commute 15, .braid 6, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .braid
    13, .braid 15, .commute 17, .commute 18, .commute 11, .commute 12, .commute 13, .commute 10,
    .commute 3, .commute 4, .commute 5, .braid 6, .commute 8, .commute 1, .commute 2, .commute
    3, .commute 4, .commute 5, .braid 6, .braid 8, .braid 10, .commute 12, .braid 13, .commute
    15, .commute 16, .commute 17, .braid 18, .braid 20, .braid 22, .commute 24, .commute 25,
    .square 26, .commute 7, .braid 5, .braid 7, .commute 9, .commute 10])
,
  ([5, 0, 2, 1, 8, 5, 0, 6, 5, 1, 0, 6, 8, 2, 1, 0, 5, 6, 1, 2, 0, 1, 8, 0, 5, 1, 0, 1, 2], [2,
    0, 5, 6, 8, 0, 1, 2, 0, 5, 8, 0, 8, 1, 6, 5, 0, 8, 5, 6, 2, 1, 0, 5, 1, 2, 0], [.commute 11,
    .commute 12, .commute 13, .commute 14, .braid 15, .commute 17, .commute 18, .commute 8,
    .commute 6, .commute 3, .commute 4, .commute 5, .braid 6, .braid 8, .commute 10, .commute
    11, .commute 12, .braid 13, .commute 15, .commute 3, .commute 4, .commute 1, .commute 0,
    .braid 1, .commute 3, .braid 4, .commute 6, .commute 7, .braid 8, .commute 10, .braid 11,
    .commute 13, .commute 14, .braid 15, .commute 17, .braid 18, .commute 20, .commute 21,
    .braid 22, .braid 24, .square 26, .commute 25, .commute 20, .commute 17, .commute 18,
    .commute 19, .commute 14, .commute 15, .braid 12, .commute 14, .braid 15, .commute 17,
    .commute 18, .commute 11, .braid 12, .commute 14, .braid 15, .commute 17, .commute 9,
    .commute 10, .commute 8, .commute 7, .braid 8, .braid 10])
,
  ([2, 0, 5, 6, 8, 0, 1, 2, 0, 5, 8, 0, 8, 1, 6, 5, 0, 8, 5, 6, 2, 1, 0, 5, 1, 2, 0], [0, 5, 2,
    1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [.commute 12,
    .commute 13, .commute 14, .braid 15, .commute 12, .commute 13, .commute 11, .commute 9,
    .commute 3, .commute 4, .commute 5, .commute 6, .commute 7, .commute 8, .braid 9, .braid 11,
    .braid 13, .commute 15, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10,
    .commute 11, .braid 4, .commute 6, .commute 7, .commute 8, .commute 3, .braid 4, .commute 0,
    .commute 1])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0, 2, 1, 0, 8,
    0, 1, 2], [0, 5, 2, 8, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5, 6, 1, 0, 5, 1, 2, 1, 0, 8, 1, 0, 5, 0,
    1, 2, 0], [.commute 25, .square 26, .braid 24, .square 26, .commute 25, .braid 26, .commute
    28, .braid 22, .commute 24, .commute 15, .braid 13, .braid 15, .commute 17, .commute 18,
    .commute 19, .commute 20, .commute 21, .braid 22, .commute 20, .commute 11, .commute 10,
    .braid 11, .commute 13, .commute 14, .braid 15, .commute 17, .commute 18, .commute 8,
    .commute 9, .commute 7, .commute 8, .braid 9, .commute 11, .commute 12, .commute 13,
    .commute 14, .braid 15, .commute 17, .braid 18, .braid 20, .commute 22, .commute 17,
    .commute 18, .commute 12, .braid 4, .commute 6, .commute 7, .commute 8, .commute 9, .braid
    10, .braid 12, .commute 14, .commute 15, .commute 3, .braid 4, .commute 6, .commute 7,
    .braid 8, .commute 10, .commute 11, .braid 12, .commute 14, .braid 15, .commute 17])
,
  ([0, 5, 2, 8, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5, 6, 1, 0, 5, 1, 2, 1, 0, 8, 1, 0, 5, 0, 1, 2, 0],
    [2, 5, 0, 8, 1, 0, 5, 0, 6, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [.braid 18, .commute 20, .commute 21, .commute 14, .commute 15, .commute 13, .braid 11,
    .braid 13, .braid 15, .commute 17, .commute 18, .commute 19, .commute 20, .commute 16,
    .commute 17, .commute 14, .commute 15, .commute 12, .commute 13, .commute 6, .commute 7,
    .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .braid 13, .braid 15, .braid
    17, .commute 19, .braid 8, .commute 10, .commute 11, .commute 12, .commute 13, .commute 7,
    .braid 8, .commute 10, .commute 5, .commute 6, .commute 4, .commute 3, .braid 4, .braid 6,
    .commute 8, .commute 9, .braid 10, .commute 12, .braid 13, .commute 15, .commute 16, .braid
    17, .commute 15, .commute 3, .commute 4, .commute 5, .commute 6, .braid 7, .commute 1,
    .commute 0, .braid 1, .commute 3, .commute 4, .braid 5])
,
  ([2, 5, 0, 8, 1, 0, 5, 0, 6, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [.commute 7, .braid 8, .commute 10, .commute 11, .commute 12, .braid 13, .braid 15, .commute
    17, .commute 11, .commute 12, .commute 13, .commute 10, .braid 6, .commute 8, .commute 9,
    .commute 5, .braid 6, .commute 8, .commute 3, .commute 4, .commute 5, .braid 6, .commute 3,
    .commute 4, .commute 0, .commute 1, .commute 2, .commute 3, .commute 1])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0, 1,
    2, 1], [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2,
    0], [.commute 28, .braid 26, .braid 28, .square 30, .square 29, .commute 27])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0, 1, 2,
    1], [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2,
    0], [.commute 27, .braid 28, .square 30, .braid 26, .commute 28])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0, 5,
    1, 0, 8, 0, 5, 1], [5, 6, 0, 5, 2, 8, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5, 6, 1, 0, 5, 8, 1, 0, 1,
    2, 5, 8, 0, 1, 8, 0, 5, 1], [.braid 24, .commute 26, .commute 27, .commute 23, .braid 24,
    .commute 26, .braid 27, .square 29, .commute 22, .commute 23, .braid 24, .commute 26, .braid
    27, .square 29, .commute 17, .braid 15, .braid 17, .commute 19, .commute 20, .commute 21,
    .commute 13, .commute 12, .braid 13, .commute 15, .commute 16, .braid 17, .commute 19,
    .commute 10, .commute 11, .commute 9, .commute 10, .braid 11, .commute 13, .commute 14,
    .commute 15, .commute 16, .braid 17, .braid 19, .braid 21, .commute 23, .commute 24,
    .commute 25, .commute 14, .braid 6, .commute 8, .commute 9, .commute 10, .commute 11, .braid
    12, .braid 14, .commute 16, .commute 17, .commute 5, .braid 6, .commute 8, .commute 9,
    .braid 10, .commute 12, .commute 13, .braid 14, .commute 16, .braid 17, .commute 19,
    .commute 20])
,
  ([5, 6, 0, 5, 2, 8, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5, 6, 1, 0, 5, 8, 1, 0, 1, 2, 5, 8, 0, 1, 8, 0,
    5, 1], [5, 6, 0, 5, 8, 0, 1, 2, 6, 0, 5, 8, 0, 8, 1, 6, 5, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2,
    0], [.braid 21, .commute 23, .commute 19, .commute 12, .commute 4, .commute 5, .braid 6,
    .commute 8, .commute 9, .braid 10, .braid 12, .commute 14, .commute 15, .commute 16, .braid
    17, .braid 19, .commute 21, .commute 22, .braid 23, .braid 25, .commute 27, .square 28,
    .braid 26, .commute 28, .square 29, .commute 24, .commute 25, .braid 26, .commute 22,
    .commute 23, .braid 20, .commute 22, .braid 23, .commute 25, .commute 26, .commute 18,
    .commute 19, .braid 20, .commute 22, .braid 23, .commute 25, .commute 18, .braid 16, .braid
    18, .commute 20, .commute 21, .commute 22, .braid 23, .commute 15, .commute 16, .braid 13,
    .commute 15, .braid 16, .commute 18, .commute 19, .commute 11, .commute 12, .braid 13,
    .commute 15, .braid 16, .commute 18, .commute 11, .braid 9, .braid 11])
,
  ([5, 6, 0, 5, 8, 0, 1, 2, 6, 0, 5, 8, 0, 8, 1, 6, 5, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0], [5,
    6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [.commute 13, .commute 14, .commute 15, .braid 16, .commute 13, .commute 14, .commute 12,
    .commute 10, .commute 8, .commute 9, .braid 10, .braid 12, .braid 14, .commute 16, .commute
    7, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .braid 5, .commute 7,
    .commute 8, .commute 9, .commute 4, .braid 5])
,
  ([5, 6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0, 5, 1,
    0, 8, 0, 5, 1], [5, 6, 0, 5, 8, 0, 1, 2, 6, 5, 0, 8, 1, 5, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 5,
    0, 8, 1, 0, 5], [.braid 23, .commute 25, .commute 26, .commute 22, .braid 23, .commute 25,
    .braid 26, .square 28, .commute 21, .commute 22, .braid 23, .commute 25, .braid 26, .square
    28, .commute 27, .commute 16, .braid 14, .braid 16, .commute 18, .commute 19, .commute 20,
    .commute 12, .commute 11, .braid 12, .commute 14, .commute 15, .braid 16, .commute 18,
    .commute 9, .commute 10, .commute 8, .commute 9, .braid 10, .commute 12, .commute 13,
    .commute 14, .commute 15, .braid 16, .braid 18, .braid 20, .commute 22, .commute 23,
    .commute 24, .braid 25, .braid 27, .commute 29, .square 30, .commute 13, .braid 5, .commute
    7, .commute 8, .commute 9, .commute 10, .braid 11, .braid 13, .commute 15, .commute 16,
    .commute 4, .braid 5, .commute 7, .commute 8, .braid 9, .commute 11, .commute 12])
,
  ([5, 6, 0, 5, 8, 0, 1, 2, 6, 5, 0, 8, 1, 5, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5],
    [5, 6, 0, 5, 8, 0, 1, 2, 6, 1, 0, 5, 8, 0, 6, 1, 5, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [.braid 13, .commute 15, .braid 16, .commute 18, .commute 19, .braid 20, .commute 22, .braid
    23, .commute 25, .commute 26, .braid 27, .commute 22, .commute 23, .commute 24, .commute 21,
    .commute 18, .braid 19, .braid 21, .commute 23, .braid 24, .commute 26, .commute 27, .braid
    17, .commute 19, .commute 20, .braid 21, .commute 23, .braid 24, .commute 26, .commute 19,
    .commute 16, .braid 17, .braid 19, .commute 21, .commute 22, .commute 23, .braid 24,
    .commute 15, .commute 16, .commute 17, .commute 14, .commute 11, .braid 12, .braid 14,
    .commute 16, .braid 17, .commute 19, .commute 20, .braid 10, .commute 12, .commute 13,
    .braid 14, .commute 16, .braid 17, .commute 19, .commute 12, .commute 9, .braid 10, .braid
    12, .commute 14, .commute 15, .commute 16, .braid 17, .commute 14])
,
  ([5, 6, 0, 5, 8, 0, 1, 2, 6, 1, 0, 5, 8, 0, 6, 1, 5, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [.commute 15, .commute 13, .commute 11, .commute 8, .commute 9, .commute 10, .braid 11,
    .braid 13, .braid 15, .commute 17, .braid 6, .commute 8, .commute 9, .commute 10, .commute
    11, .commute 12, .commute 13, .commute 5, .braid 6, .commute 8, .commute 9, .commute 10,
    .commute 4, .commute 5, .braid 6])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0, 0,
    1, 0], [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1,
    2, 1, 0], [.square 29])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0,
    0, 1, 0], [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0,
    1, 2, 0], [.square 30, .square 29])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0, 1,
    0, 8, 0, 1], [5, 0, 2, 1, 8, 5, 0, 6, 5, 1, 0, 8, 2, 1, 0, 5, 6, 5, 1, 2, 0, 1, 8, 0, 5, 8,
    0, 1, 2, 1, 0, 8, 1, 0, 1], [.braid 29, .commute 31, .commute 17, .braid 15, .braid 17,
    .commute 19, .commute 20, .commute 21, .commute 22, .commute 13, .commute 12, .braid 13,
    .commute 15, .commute 16, .braid 17, .commute 19, .commute 20, .commute 15, .braid 6,
    .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .braid 13, .braid 15,
    .commute 17, .commute 18, .commute 11, .commute 12, .commute 13, .commute 10, .commute 3,
    .commute 4, .commute 5, .braid 6, .commute 8, .commute 1, .commute 2, .commute 3, .commute
    4, .commute 5, .braid 6, .braid 8, .braid 10, .commute 12, .braid 13, .commute 15, .commute
    16, .commute 17, .braid 18, .braid 20, .braid 22, .commute 24, .commute 7, .braid 5, .braid
    7, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .commute 14, .braid 15])
,
  ([5, 0, 2, 1, 8, 5, 0, 6, 5, 1, 0, 8, 2, 1, 0, 5, 6, 5, 1, 2, 0, 1, 8, 0, 5, 8, 0, 1, 2, 1, 0,
    8, 1, 0, 1], [2, 0, 5, 6, 8, 0, 1, 5, 0, 8, 2, 1, 0, 5, 6, 0, 5, 1, 0, 1, 2, 8, 0, 1, 5, 0,
    8, 5, 0, 1, 2, 1, 0], [.commute 17, .commute 18, .commute 8, .commute 6, .commute 3,
    .commute 4, .commute 5, .braid 6, .braid 8, .commute 10, .commute 11, .commute 12, .braid
    13, .commute 15, .commute 3, .commute 4, .commute 1, .commute 0, .braid 1, .commute 3,
    .braid 4, .commute 6, .commute 7, .braid 8, .commute 10, .braid 11, .commute 13, .commute
    14, .braid 15, .commute 17, .braid 18, .commute 20, .commute 21, .braid 22, .braid 24,
    .commute 26, .commute 27, .commute 28, .braid 29, .braid 31, .square 33, .braid 26, .commute
    28, .commute 29, .commute 25, .braid 26, .commute 28, .commute 24, .commute 25, .braid 26,
    .commute 23, .commute 24, .commute 22, .commute 20, .commute 17, .commute 18, .commute 19,
    .braid 20, .braid 22, .braid 24, .commute 26, .commute 19, .commute 20, .commute 16])
,
  ([2, 0, 5, 6, 8, 0, 1, 5, 0, 8, 2, 1, 0, 5, 6, 0, 5, 1, 0, 1, 2, 8, 0, 1, 5, 0, 8, 5, 0, 1, 2,
    1, 0], [0, 5, 8, 0, 1, 2, 5, 6, 0, 5, 1, 0, 1, 8, 0, 1, 5, 0, 6, 5, 2, 1, 0, 8, 2, 1, 0, 5,
    0, 1, 2, 1, 0], [.braid 17, .commute 19, .braid 20, .commute 22, .commute 23, .braid 24,
    .commute 22, .braid 15, .commute 17, .commute 18, .commute 19, .braid 20, .braid 22,
    .commute 24, .commute 18, .commute 19, .commute 20, .commute 17, .commute 9, .commute 10,
    .commute 8, .commute 6, .commute 0, .commute 1, .commute 2, .commute 3, .commute 4, .commute
    5, .braid 6, .braid 8, .braid 10, .commute 12, .commute 13, .commute 14, .braid 15, .braid
    17, .commute 19, .braid 20, .commute 22, .commute 23, .braid 12, .commute 14, .commute 15,
    .commute 16, .commute 17, .commute 11, .braid 12, .commute 14, .commute 15, .commute 10,
    .commute 11, .braid 12, .commute 9, .commute 10, .commute 8, .commute 5, .commute 6,
    .commute 2, .commute 3, .commute 4, .commute 5, .braid 6, .braid 8, .braid 10])
,
  ([0, 5, 8, 0, 1, 2, 5, 6, 0, 5, 1, 0, 1, 8, 0, 1, 5, 0, 6, 5, 2, 1, 0, 8, 2, 1, 0, 5, 0, 1, 2,
    1, 0], [8, 0, 5, 6, 1, 2, 0, 8, 1, 0, 5, 6, 0, 1, 8, 2, 0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5,
    0, 1, 2, 1, 0], [.commute 12, .braid 13, .braid 15, .braid 17, .commute 19, .commute 20,
    .commute 21, .commute 22, .commute 18, .commute 19, .commute 16, .commute 17, .commute 14,
    .commute 15, .commute 5, .commute 6, .commute 7, .commute 8, .commute 4, .commute 5,
    .commute 1, .braid 2, .commute 4, .braid 5, .commute 7, .braid 8, .commute 10, .commute 11,
    .commute 12, .commute 13, .commute 14, .braid 15, .braid 17, .braid 19, .commute 21, .braid
    10, .commute 12, .commute 13, .commute 14, .commute 15, .commute 7, .commute 8, .commute 9,
    .braid 10, .commute 12, .commute 8, .commute 6, .braid 0, .commute 2, .commute 3, .commute
    4, .commute 5, .braid 6, .braid 8, .commute 10, .commute 11, .braid 12, .commute 14, .braid
    15, .commute 17, .commute 18, .braid 19, .commute 17, .commute 14])
,
  ([8, 0, 5, 6, 1, 2, 0, 8, 1, 0, 5, 6, 0, 1, 8, 2, 0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2,
    1, 0], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5,
    0, 1, 2, 1, 0], [.commute 15, .commute 16, .commute 13, .commute 11, .commute 12, .braid 9,
    .commute 11, .commute 7, .commute 8, .braid 9, .commute 7, .commute 5, .commute 6])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2,
    1, 0, 1, 0, 8, 0, 1], [8, 0, 5, 6, 1, 2, 8, 0, 1, 5, 0, 8, 0, 2, 1, 0, 5, 6, 0, 1, 2, 5, 0,
    1, 8, 0, 5, 8, 0, 1, 2, 0, 1, 8, 0, 1], [.braid 31, .square 33, .braid 19, .commute 21,
    .commute 22, .commute 23, .commute 24, .commute 16, .commute 17, .commute 18, .braid 19,
    .commute 21, .commute 22, .commute 17, .commute 15, .braid 9, .commute 11, .commute 12,
    .commute 13, .commute 14, .braid 15, .braid 17, .commute 19, .commute 20, .commute 14,
    .commute 15, .commute 6, .commute 7, .commute 8, .braid 9, .commute 11, .braid 12, .commute
    14, .braid 15, .commute 17, .commute 18, .commute 19, .braid 20, .braid 22, .braid 24,
    .commute 26, .commute 11, .commute 12, .commute 13, .commute 14, .commute 15, .commute 16,
    .braid 17, .commute 19, .commute 20, .commute 10, .commute 7, .braid 8, .braid 10, .commute
    12, .commute 13, .commute 14, .braid 15, .commute 17, .commute 5, .braid 6, .commute 8,
    .commute 9, .braid 10])
,
  ([8, 0, 5, 6, 1, 2, 8, 0, 1, 5, 0, 8, 0, 2, 1, 0, 5, 6, 0, 1, 2, 5, 0, 1, 8, 0, 5, 8, 0, 1, 2,
    0, 1, 8, 0, 1], [0, 8, 5, 0, 1, 2, 6, 5, 0, 6, 1, 8, 0, 5, 6, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5,
    8, 0, 1, 2, 8, 0, 1, 0, 1], [.commute 12, .braid 13, .commute 15, .commute 16, .braid 17,
    .commute 19, .braid 20, .commute 22, .commute 23, .braid 24, .braid 26, .commute 28,
    .commute 29, .commute 22, .commute 11, .commute 12, .commute 10, .commute 8, .commute 5,
    .commute 6, .commute 7, .braid 8, .braid 10, .braid 12, .commute 14, .commute 15, .commute
    7, .commute 8, .commute 4, .braid 5, .commute 7, .braid 8, .commute 10, .commute 11, .braid
    12, .commute 14, .braid 15, .commute 17, .commute 18, .commute 19, .braid 20, .braid 22,
    .commute 24, .commute 25, .braid 26, .commute 28, .braid 29, .commute 31, .square 32,
    .commute 18, .commute 19, .commute 20, .commute 17, .commute 3, .commute 4, .commute 5,
    .commute 6, .commute 2, .braid 0, .braid 2, .commute 4, .commute 5, .braid 6, .commute 8])
,
  ([0, 8, 5, 0, 1, 2, 6, 5, 0, 6, 1, 8, 0, 5, 6, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 8, 0, 1, 2, 8, 0,
    1, 0, 1], [0, 8, 5, 0, 1, 6, 5, 2, 1, 0, 8, 0, 5, 6, 1, 2, 0, 1, 5, 0, 8, 6, 2, 1, 0, 5, 0,
    1, 2, 0], [.commute 9, .commute 10, .commute 11, .braid 12, .commute 14, .braid 15, .braid
    17, .commute 19, .braid 20, .commute 22, .commute 23, .commute 24, .commute 25, .braid 26,
    .commute 28, .braid 29, .square 31, .square 30, .commute 27, .commute 26, .braid 24, .braid
    22, .commute 24, .commute 19, .commute 20, .commute 21, .braid 22, .commute 20, .commute 18,
    .commute 16, .commute 17, .braid 18, .braid 20, .commute 22, .commute 17, .commute 18,
    .braid 15, .commute 17, .braid 18, .commute 20, .commute 21, .commute 13, .commute 14,
    .commute 15, .commute 12, .commute 13, .braid 10, .braid 8, .commute 10, .braid 11, .braid
    13, .braid 15, .commute 17, .commute 18, .commute 19, .commute 20, .commute 16, .commute 17,
    .commute 14, .commute 15, .commute 12, .commute 13, .commute 5, .commute 6])
,
  ([0, 8, 5, 0, 1, 6, 5, 2, 1, 0, 8, 0, 5, 6, 1, 2, 0, 1, 5, 0, 8, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [2, 5, 0, 8, 1, 0, 6, 5, 6, 0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [.commute 4, .commute 5, .braid 6, .commute 8, .commute 9, .commute 10, .commute 11,
    .commute 12, .braid 13, .braid 15, .braid 17, .commute 19, .braid 8, .commute 10, .commute
    11, .commute 12, .commute 13, .commute 5, .commute 6, .commute 7, .braid 8, .commute 10,
    .commute 6, .commute 3, .commute 4, .commute 1, .commute 2, .commute 3, .braid 4, .braid 6,
    .commute 8, .commute 9, .braid 10, .commute 12, .braid 13, .commute 15, .commute 16, .braid
    17, .commute 15, .commute 2, .commute 3, .commute 4, .commute 5, .commute 6, .braid 7,
    .commute 1, .commute 0, .braid 1, .commute 3, .commute 4, .braid 5, .commute 7, .braid 8,
    .commute 10, .commute 11, .commute 12, .braid 13, .braid 15, .commute 17, .commute 11,
    .commute 12, .commute 13, .commute 10, .braid 6])
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
