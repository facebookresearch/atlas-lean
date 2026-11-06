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
/-- Exact bounded chunks of literal E8 square, commutation and braid moves, block 3. -/
def y431AuxE8RewriteData03 : Fin 64 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
![
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1, 0,
    5], [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1,
    2, 0], [.braid 23, .commute 25, .commute 26, .commute 27, .braid 28, .braid 25, .commute 27,
    .commute 28, .commute 24, .braid 25, .commute 27, .commute 23, .commute 24, .braid 25])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0,
    6], [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2,
    0], [.commute 22, .commute 23, .commute 24, .commute 21, .commute 22, .commute 20, .braid
    18, .braid 20, .braid 22, .braid 24, .commute 26, .commute 27, .commute 28, .commute 29,
    .square 30, .commute 23, .commute 21, .commute 22, .commute 19, .commute 20, .commute 21])
,
  ([5, 1, 0, 8, 0, 5, 1, 1, 2, 1], [5, 1, 0, 8, 0, 5, 2, 1], [.square 6])
,
  ([1, 2, 1, 5, 1, 0, 8, 0, 5, 2, 1], [5, 1, 0, 8, 0, 5, 1], [.commute 2, .square 3, .commute 1,
    .commute 2, .commute 3, .commute 4, .commute 5, .square 6, .commute 0])
,
  ([1, 2, 1, 5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1,
    2, 0], [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0,
    1, 2, 0], [.braid 0, .commute 2, .commute 3, .commute 4, .commute 5, .square 6, .commute 5,
    .commute 1, .commute 2, .braid 3, .braid 5, .commute 7, .braid 8, .commute 10, .braid 11,
    .commute 13, .braid 14, .commute 16, .commute 17, .commute 4, .commute 0, .commute 1,
    .commute 2, .commute 3])
,
  ([0, 2, 1, 0, 5, 0, 1, 2, 6, 5, 0, 1, 2, 8, 0, 1, 2, 5, 0, 1, 6, 5, 0, 8, 0, 1, 2, 5, 0, 6,
    5], [2, 1, 0, 5, 0, 1, 6, 5, 0, 8, 0, 5, 1, 0, 2, 1, 6, 5, 0, 2, 8, 0, 5, 6, 1, 0, 5, 0, 1,
    2, 0], [.commute 28, .commute 7, .commute 8, .commute 9, .braid 10, .commute 12, .braid 13,
    .commute 15, .braid 16, .commute 18, .braid 19, .commute 21, .commute 22, .commute 23,
    .commute 24, .commute 25, .braid 26, .braid 28, .commute 25, .commute 26, .commute 27,
    .commute 28, .commute 24, .commute 25, .commute 11, .commute 12, .braid 13, .commute 15,
    .braid 16, .commute 18, .braid 19, .commute 21, .braid 22, .commute 24, .braid 25, .commute
    27, .commute 10, .braid 11, .commute 13, .braid 14, .commute 16, .braid 17, .commute 19,
    .commute 20, .commute 21, .braid 22, .commute 24, .braid 25, .commute 13, .commute 14,
    .commute 12, .commute 0, .braid 1, .commute 3, .braid 4, .commute 6, .braid 7, .commute 9,
    .braid 10, .braid 12, .braid 14, .commute 16, .commute 17, .commute 18])
,
  ([2, 1, 0, 5, 0, 1, 6, 5, 0, 8, 0, 5, 1, 0, 2, 1, 6, 5, 0, 2, 8, 0, 5, 6, 1, 0, 5, 0, 1, 2,
    0], [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1,
    2, 0], [.commute 19, .commute 20, .commute 21, .commute 22, .commute 15, .commute 16,
    .commute 13, .commute 14, .commute 11, .commute 12, .braid 2, .commute 4, .braid 5, .commute
    7, .commute 8, .commute 9, .commute 10, .commute 11, .braid 12, .braid 14, .braid 16,
    .commute 18, .commute 11, .commute 12, .commute 13, .commute 14, .commute 10, .commute 11,
    .commute 1, .braid 2, .commute 4, .braid 5, .commute 7, .braid 8, .commute 10, .braid 11,
    .commute 13, .braid 14, .commute 16, .commute 17, .commute 3, .commute 4, .commute 0,
    .commute 1, .commute 2, .commute 3, .commute 1])
,
  ([5, 1, 0, 8, 0, 5, 1, 5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1,
    0, 5, 0, 1, 2, 0], [5, 6, 0, 8, 1, 2, 1, 0, 5, 6, 0, 1, 2, 8, 0, 1, 5, 0, 8, 1, 0, 5, 6, 2,
    1, 2, 0, 5, 0, 1, 2], [.commute 5, .square 6, .braid 2, .commute 4, .commute 5, .commute 1,
    .braid 2, .commute 4, .braid 5, .commute 7, .commute 8, .commute 9, .braid 10, .square 12,
    .commute 16, .commute 17, .commute 15, .commute 3, .commute 4, .commute 2, .commute 1,
    .braid 2, .braid 4, .commute 6, .braid 7, .commute 9, .commute 10, .commute 11, .commute 12,
    .braid 13, .braid 15, .braid 17, .commute 19, .commute 20, .braid 21, .commute 23, .commute
    24, .braid 25, .commute 27, .braid 28, .commute 30, .square 31, .commute 10, .commute 11,
    .commute 12, .commute 13, .commute 6, .commute 7, .braid 8, .commute 10, .commute 5, .braid
    6, .commute 8, .commute 9, .braid 10, .commute 12, .braid 13, .commute 15, .commute 16,
    .braid 17, .braid 19, .commute 21, .commute 22, .braid 23])
,
  ([5, 6, 0, 8, 1, 2, 1, 0, 5, 6, 0, 1, 2, 8, 0, 1, 5, 0, 8, 1, 0, 5, 6, 2, 1, 2, 0, 5, 0, 1,
    2], [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2,
    0, 1], [.commute 25, .commute 26, .commute 27, .braid 28, .braid 4, .commute 6, .commute 7,
    .commute 8, .commute 9, .braid 10, .commute 12, .braid 13, .braid 15, .commute 17, .commute
    18, .braid 19, .commute 21, .commute 22, .braid 23, .commute 25, .braid 26, .commute 28,
    .commute 14, .commute 11, .commute 12, .commute 13, .commute 10, .commute 8, .commute 9,
    .braid 6, .commute 8, .commute 3, .commute 4, .commute 5, .braid 6, .commute 4, .commute 3])
,
  ([1, 0, 2, 1, 0, 5, 0, 1, 2, 6, 5, 0, 1, 8, 0, 1, 2, 5, 0, 1, 6, 5, 0, 8, 0, 1, 2, 5, 0, 6,
    5], [1, 2, 1, 5, 0, 1, 6, 5, 6, 0, 8, 0, 1, 2, 5, 6, 0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 1,
    2, 0], [.commute 28, .commute 12, .braid 13, .commute 15, .braid 16, .commute 18, .braid 19,
    .commute 21, .commute 22, .commute 23, .commute 24, .commute 25, .braid 26, .braid 28,
    .commute 25, .commute 26, .commute 27, .commute 28, .commute 24, .commute 25, .commute 8,
    .commute 9, .commute 10, .commute 11, .commute 12, .braid 13, .commute 15, .braid 16,
    .commute 18, .braid 19, .commute 21, .braid 22, .commute 24, .braid 25, .commute 27,
    .commute 14, .commute 15, .commute 13, .commute 1, .braid 2, .commute 4, .braid 5, .commute
    7, .braid 8, .commute 10, .braid 11, .braid 13, .braid 15, .commute 17, .commute 18,
    .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute 16, .commute 17,
    .commute 14, .commute 15, .commute 12, .commute 13, .braid 3, .commute 5, .braid 6])
,
  ([1, 2, 1, 5, 0, 1, 6, 5, 6, 0, 8, 0, 1, 2, 5, 6, 0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 1, 2,
    0], [5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1,
    2, 0], [.commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .braid 13, .braid 15,
    .braid 17, .commute 19, .commute 12, .commute 13, .commute 14, .commute 15, .commute 11,
    .commute 12, .commute 2, .braid 3, .commute 5, .braid 6, .commute 8, .braid 9, .commute 11,
    .braid 12, .commute 14, .braid 15, .commute 17, .commute 18, .commute 4, .commute 5,
    .commute 1, .commute 2, .commute 3, .commute 4, .commute 2, .commute 0, .commute 1])
,
  ([5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0,
    5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 0, 1, 6, 5, 0, 1, 2, 1, 0, 5, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 0, 1, 2, 0], [.commute 27, .commute 28, .braid 25, .commute 27, .braid 28,
    .square 30, .commute 23, .commute 24, .commute 25, .commute 26, .commute 22, .commute 21,
    .braid 22, .commute 24, .commute 25, .braid 26, .commute 28, .square 29, .square 28, .square
    27, .commute 25, .square 26, .commute 24, .square 25, .commute 23, .square 24, .commute 18,
    .commute 19, .commute 20, .commute 21, .commute 22, .square 23, .commute 17, .braid 15,
    .braid 17, .commute 19, .commute 14, .commute 15, .braid 12, .commute 14, .braid 15,
    .commute 17, .commute 18, .braid 19, .commute 21, .square 22, .commute 11, .commute 12,
    .commute 13, .braid 9, .commute 11, .commute 12, .braid 13, .commute 15, .commute 16,
    .commute 17, .commute 18, .braid 19, .square 21, .square 20, .commute 12, .commute 13,
    .commute 14, .braid 15])
,
  ([5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 0, 1, 6, 5, 0, 1, 2, 1, 0, 5, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6,
    2, 1, 0, 5, 0, 1, 2, 0], [1, 0, 2, 2, 0], [.commute 11, .commute 12, .braid 13, .commute 15,
    .braid 16, .commute 18, .square 19, .commute 10, .braid 11, .commute 13, .commute 14,
    .commute 15, .braid 16, .square 18, .square 17, .braid 13, .commute 15, .square 16, .commute
    12, .braid 13, .square 15, .square 14, .commute 8, .commute 9, .commute 10, .commute 11,
    .commute 12, .square 13, .square 12, .commute 4, .commute 5, .braid 6, .commute 8, .commute
    1, .commute 2, .commute 3, .commute 4, .commute 5, .braid 6, .braid 8, .commute 10, .square
    11, .commute 9, .square 10, .commute 7, .commute 8, .square 9, .square 8, .commute 2, .braid
    3, .commute 5, .commute 0, .commute 1, .commute 2, .braid 3, .braid 5, .square 7, .square 6,
    .commute 4, .square 5, .braid 2, .square 4, .square 3, .commute 1])
,
  ([1, 0, 2, 2, 0], [1], [.square 2, .square 1])
,
  ([1, 5, 0, 8, 0, 1, 5], [5, 1, 0, 8, 0, 5, 1], [.commute 5, .commute 0])
,
  ([5, 1, 0, 8, 0, 5, 1, 5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2,
    1, 0, 5, 0, 1, 2, 0], [5, 6, 0, 8, 1, 2, 1, 0, 5, 6, 0, 1, 2, 8, 0, 1, 5, 0, 8, 2, 1, 0, 5,
    1, 6, 2, 1, 0, 5, 0, 1, 2], [.commute 5, .square 6, .braid 2, .commute 4, .commute 5,
    .commute 1, .braid 2, .commute 4, .braid 5, .commute 7, .commute 8, .commute 9, .braid 10,
    .square 12, .commute 16, .commute 17, .commute 15, .commute 3, .commute 4, .commute 2,
    .commute 1, .braid 2, .braid 4, .commute 6, .braid 7, .commute 9, .commute 10, .commute 11,
    .commute 12, .braid 13, .braid 15, .braid 17, .commute 19, .commute 20, .commute 21, .braid
    22, .commute 24, .commute 25, .braid 26, .commute 28, .braid 29, .commute 31, .square 32,
    .commute 10, .commute 11, .commute 12, .commute 13, .commute 6, .commute 7, .braid 8,
    .commute 10, .commute 5, .braid 6, .commute 8, .commute 9, .braid 10, .commute 12, .braid
    13, .commute 15, .commute 16, .braid 17, .commute 19, .braid 20, .commute 22])
,
  ([5, 6, 0, 8, 1, 2, 1, 0, 5, 6, 0, 1, 2, 8, 0, 1, 5, 0, 8, 2, 1, 0, 5, 1, 6, 2, 1, 0, 5, 0, 1,
    2], [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1,
    2, 0, 1], [.commute 23, .braid 24, .commute 26, .commute 27, .commute 28, .braid 29, .braid
    4, .commute 6, .commute 7, .commute 8, .commute 9, .braid 10, .commute 12, .braid 13, .braid
    15, .commute 17, .commute 18, .commute 19, .braid 20, .commute 22, .commute 23, .braid 24,
    .commute 26, .braid 27, .commute 29, .commute 14, .commute 11, .commute 12, .commute 13,
    .commute 10, .commute 8, .commute 9, .braid 6, .commute 8, .commute 3, .commute 4, .commute
    5, .braid 6, .commute 4, .commute 3])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0,
    5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0,
    1], [5, 6, 0, 5, 2, 1, 0, 8, 5, 0, 1, 2, 6, 5, 0, 1, 2, 5, 0, 6, 5, 6, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0, 1], [.braid 25, .commute 27, .commute 28,
    .commute 24, .braid 25, .commute 27, .braid 28, .square 30, .commute 22, .commute 21, .braid
    22, .commute 24, .commute 25, .commute 26, .commute 20, .commute 21, .braid 22, .commute 24,
    .commute 25, .braid 26, .commute 28, .square 29, .square 28, .square 27, .commute 25,
    .square 26, .commute 24, .square 25, .commute 23, .square 24, .commute 17, .commute 18,
    .commute 19, .commute 20, .commute 21, .commute 22, .square 23, .commute 16, .braid 14,
    .braid 16, .commute 18, .commute 19, .commute 13, .commute 14, .braid 11, .commute 13,
    .braid 14, .commute 16, .commute 17, .commute 10, .commute 11, .commute 12, .braid 8,
    .commute 10, .commute 11, .braid 12, .commute 14, .commute 15, .commute 16, .braid 17,
    .braid 19, .commute 21, .square 22, .commute 18])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 5, 0, 1, 2, 6, 5, 0, 1, 2, 5, 0, 6, 5, 6, 5, 6, 1, 0, 5, 2, 1, 0, 8,
    2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0, 1], [5, 2, 1, 0, 5, 1, 0, 1, 0, 5, 0, 1, 2, 0, 1],
    [.braid 19, .square 21, .square 20, .commute 11, .commute 12, .commute 13, .braid 14,
    .commute 16, .commute 10, .commute 11, .braid 12, .commute 14, .commute 9, .braid 10,
    .commute 12, .commute 13, .braid 14, .braid 16, .commute 18, .square 19, .commute 15, .braid
    16, .square 18, .square 17, .commute 13, .braid 11, .braid 13, .commute 15, .square 16,
    .commute 12, .braid 13, .square 15, .square 14, .commute 7, .commute 8, .commute 9, .commute
    10, .commute 11, .commute 12, .square 13, .braid 10, .square 12, .square 11, .commute 3,
    .commute 4, .braid 5, .commute 7, .commute 1, .commute 2, .commute 3, .commute 4, .braid 5,
    .braid 7, .commute 9, .square 10, .commute 8, .square 9, .commute 6, .commute 7, .square 8,
    .square 7, .commute 1, .braid 2, .commute 4])
,
  ([5, 2, 1, 0, 5, 1, 0, 1, 0, 5, 0, 1, 2, 0, 1], [1], [.commute 0, .commute 1, .braid 2, .braid
    4, .square 6, .square 5, .commute 3, .square 4, .braid 1, .square 3, .square 2, .commute 0,
    .square 1, .square 0])
,
  ([8, 1], [8, 1], [])
,
  ([1, 8], [8, 1], [.commute 0])
,
  ([8, 1, 1], [8], [.square 1])
,
  ([1, 2, 1, 0, 1, 0], [1, 2, 0, 1], [.braid 2, .square 4])
,
  ([1, 2, 0, 1, 1, 2, 1], [0, 1, 0], [.square 3, .commute 1, .square 2, .braid 0])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0,
    1], [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1,
    2, 0, 1], [])
,
  ([6, 5, 1, 0, 8, 0, 5, 6, 1, 5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5,
    6, 2, 1, 0, 5, 0, 1, 2, 0, 1], [6, 5, 6, 0, 8, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 2, 0, 1, 5, 0,
    8, 2, 1, 0, 5, 6, 0, 2, 1, 0, 5, 1, 2, 0, 1], [.commute 7, .commute 6, .braid 7, .square 9,
    .braid 8, .commute 10, .braid 11, .commute 13, .braid 3, .commute 5, .commute 6, .commute 2,
    .braid 3, .commute 5, .braid 6, .commute 8, .commute 9, .commute 10, .braid 11, .braid 13,
    .commute 15, .commute 16, .square 17, .commute 16, .braid 14, .braid 16, .commute 18,
    .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .braid 25,
    .commute 27, .commute 28, .braid 29, .square 31, .commute 17, .commute 18, .commute 15,
    .commute 16, .commute 13, .commute 14, .commute 4, .commute 5, .commute 3, .commute 2,
    .braid 3, .braid 5, .commute 7, .braid 8, .commute 10, .commute 11, .commute 12, .commute
    13, .braid 14, .braid 16, .braid 18, .commute 20, .commute 21, .commute 22, .braid 23,
    .commute 25])
,
  ([6, 5, 6, 0, 8, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 2, 0, 1, 5, 0, 8, 2, 1, 0, 5, 6, 0, 2, 1, 0, 5,
    1, 2, 0, 1], [5, 6, 5, 2, 0, 5, 8, 0, 1, 2, 0, 8, 5, 0, 1, 6, 5, 0, 8, 2, 1, 0, 5, 6, 2, 1,
    0, 5, 1, 0, 1], [.commute 26, .braid 27, .commute 29, .square 30, .commute 11, .commute 12,
    .commute 13, .commute 14, .commute 7, .commute 8, .braid 9, .commute 11, .commute 6, .braid
    7, .commute 9, .commute 10, .braid 11, .commute 13, .braid 14, .commute 16, .commute 17,
    .braid 18, .commute 20, .braid 21, .commute 23, .commute 24, .braid 25, .commute 27,
    .commute 28, .square 29, .braid 5, .commute 7, .commute 8, .commute 9, .commute 10, .braid
    11, .commute 13, .braid 14, .braid 16, .commute 18, .commute 19, .commute 20, .braid 21,
    .commute 23, .commute 24, .braid 25, .commute 27, .commute 9, .commute 10, .commute 11,
    .commute 12, .commute 13, .commute 14, .braid 7, .commute 9, .commute 10, .commute 11,
    .commute 6, .braid 7, .commute 9, .commute 4, .commute 5, .commute 3, .braid 0])
,
  ([5, 6, 5, 2, 0, 5, 8, 0, 1, 2, 0, 8, 5, 0, 1, 6, 5, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 0,
    1], [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 0],
    [.commute 2, .braid 3, .braid 5, .commute 7, .commute 8, .braid 9, .braid 11, .commute 13,
    .braid 14, .commute 16, .commute 17, .commute 18, .commute 19, .commute 20, .braid 21,
    .commute 23, .commute 24, .braid 25, .braid 27, .square 29, .commute 13, .commute 14,
    .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .commute 11,
    .braid 6, .commute 8, .commute 9, .commute 10, .commute 5, .braid 6, .commute 2, .commute
    3])
,
  ([0, 1, 5, 0, 1, 2, 6, 5, 0, 1, 2, 8, 0, 1, 2, 5, 0, 1, 6, 5, 0, 8, 0, 1, 2, 5, 0, 6, 5], [0,
    5, 0, 1, 6, 5, 0, 8, 0, 5, 1, 0, 2, 1, 6, 5, 0, 8, 0, 2, 5, 6, 1, 0, 5, 0, 1, 2, 0],
    [.commute 26, .commute 5, .commute 6, .commute 7, .braid 8, .commute 10, .braid 11, .commute
    13, .braid 14, .commute 16, .braid 17, .commute 19, .commute 20, .commute 21, .commute 22,
    .commute 23, .braid 24, .braid 26, .commute 23, .commute 24, .commute 25, .commute 26,
    .commute 22, .commute 23, .commute 9, .commute 10, .braid 11, .commute 13, .braid 14,
    .commute 16, .braid 17, .commute 19, .braid 20, .commute 22, .braid 23, .commute 25,
    .commute 8, .braid 9, .commute 11, .braid 12, .commute 14, .braid 15, .commute 17, .commute
    18, .commute 19, .braid 20, .commute 22, .braid 23, .commute 11, .commute 12, .commute 10,
    .commute 1, .braid 2, .commute 4, .braid 5, .commute 7, .braid 8, .braid 10, .braid 12,
    .commute 14, .commute 15, .commute 16, .commute 17, .commute 18])
,
  ([0, 5, 0, 1, 6, 5, 0, 8, 0, 5, 1, 0, 2, 1, 6, 5, 0, 8, 0, 2, 5, 6, 1, 0, 5, 0, 1, 2, 0], [5,
    6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0],
    [.commute 19, .commute 20, .commute 13, .commute 14, .commute 11, .commute 12, .commute 9,
    .commute 10, .braid 0, .commute 2, .braid 3, .commute 5, .commute 6, .commute 7, .commute 8,
    .commute 9, .braid 10, .braid 12, .braid 14, .commute 16, .commute 9, .commute 10, .commute
    11, .commute 12, .commute 8, .commute 9, .commute 2, .commute 3, .commute 1])
,
  ([5, 6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0, 5, 6,
    0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0, 1],
    [5, 6, 0, 5, 1, 0, 8, 0, 1, 6, 5, 0, 1, 2, 1, 5, 0, 5, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6,
    2, 1, 0, 5, 0, 1, 2, 0, 1], [.braid 23, .commute 25, .commute 26, .commute 22, .braid 23,
    .commute 25, .braid 26, .square 28, .commute 20, .commute 19, .braid 20, .commute 22,
    .commute 23, .commute 24, .commute 18, .commute 19, .braid 20, .commute 22, .commute 23,
    .braid 24, .commute 26, .square 27, .square 26, .square 25, .commute 23, .square 24,
    .commute 22, .square 23, .commute 21, .square 22, .commute 16, .commute 17, .commute 18,
    .commute 19, .commute 20, .square 21, .braid 14, .commute 16, .commute 17, .commute 12,
    .commute 11, .braid 12, .commute 14, .commute 15, .commute 9, .commute 10, .commute 8,
    .commute 9, .braid 10, .commute 12, .commute 13, .commute 14, .braid 15, .braid 17, .commute
    19, .square 20, .commute 16, .braid 17, .square 19, .square 18, .commute 9, .commute 10,
    .commute 11, .braid 12])
,
  ([5, 6, 0, 5, 1, 0, 8, 0, 1, 6, 5, 0, 1, 2, 1, 5, 0, 5, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2,
    1, 0, 5, 0, 1, 2, 0, 1], [1, 2, 1], [.commute 14, .commute 8, .commute 9, .braid 10,
    .commute 12, .commute 7, .braid 8, .commute 10, .commute 11, .braid 12, .braid 14, .commute
    16, .square 17, .commute 13, .braid 14, .square 16, .square 15, .commute 11, .braid 9,
    .braid 11, .commute 13, .square 14, .commute 10, .braid 11, .square 13, .square 12, .commute
    6, .commute 7, .commute 8, .commute 9, .commute 10, .square 11, .braid 8, .square 10,
    .square 9, .commute 5, .commute 3, .commute 1, .commute 2, .braid 3, .braid 5, .commute 7,
    .square 8, .commute 6, .square 7, .commute 4, .commute 5, .square 6, .square 5, .commute 2,
    .braid 0, .braid 2, .square 4, .square 3, .commute 1, .square 2, .braid 0, .square 2,
    .commute 1, .square 2])
,
  ([0, 1, 0, 5, 1, 0, 8, 0, 5, 1], [5, 1, 0, 8, 0, 5, 0, 1], [.braid 0, .commute 2, .square 3,
    .braid 1, .commute 3, .braid 4, .commute 0])
,
  ([1, 0, 5, 0, 8, 0, 1, 5], [5, 1, 0, 8, 0, 5, 0, 1], [.commute 6, .braid 1, .commute 3, .braid
    4, .commute 0])
,
  ([5, 1, 0, 8, 0, 5, 0, 1, 5, 1, 0, 8, 0, 5, 1], [0, 1, 0], [.braid 4, .commute 6, .square 7,
    .square 6, .square 5, .commute 3, .square 4, .commute 0, .braid 1, .square 3, .square 2,
    .braid 0])
,
  ([0, 8, 0, 5, 1, 0, 8, 0, 5, 1], [8, 0, 5, 1, 0, 8, 5, 1], [.braid 0, .commute 2, .commute 3,
    .braid 4, .square 6])
,
  ([5, 1, 0, 8, 0, 5, 1, 8, 0, 5, 1, 0, 8, 5, 1], [0, 8, 0], [.braid 2, .commute 4, .commute 5,
    .square 6, .commute 4, .commute 1, .braid 2, .braid 4, .square 6, .commute 3, .commute 0,
    .braid 1, .braid 3, .square 5, .square 4, .commute 2, .commute 3, .square 4, .commute 2,
    .square 3, .braid 0])
,
  ([0, 1, 0], [0, 1, 0], [])
,
  ([0, 1, 0, 0, 8, 0], [0, 8, 1, 0], [.square 2, .commute 1])
,
  ([0, 8, 1, 0, 0, 1, 0], [0, 8, 0], [.square 3, .square 2])
,
  ([0, 1, 0, 1, 2, 1], [1, 2, 0, 1], [.braid 0, .square 2, .commute 1])
,
  ([1, 2, 0, 1, 0, 1, 0], [1, 2, 1], [.braid 2, .square 4, .square 3])
,
  ([0, 1, 0, 8], [1, 0, 8, 1], [.braid 0, .commute 2])
,
  ([1, 0, 8, 1, 0, 1, 0], [1, 0, 8, 0, 1], [.braid 3, .square 5])
,
  ([1, 0, 8, 0, 1], [1, 0, 8, 0, 1], [])
,
  ([1, 0, 8, 0, 1, 8], [8, 0, 1, 0], [.braid 1, .commute 3, .square 4, .commute 0, .braid 1])
,
  ([1, 0, 8, 1, 8], [0, 1, 0], [.commute 2, .square 3, .braid 0])
,
  ([5, 1, 0, 8, 0, 5, 1, 1, 0, 5, 0, 1], [5, 1, 0, 8, 5, 1], [.square 6, .braid 4, .square 6,
    .square 5])
,
  ([5, 1, 0, 8, 5, 1, 5, 1, 0, 8, 0, 5, 1], [8], [.commute 4, .square 5, .square 4, .braid 2,
    .square 4, .square 3, .commute 0, .commute 1, .square 2, .commute 0, .square 1])
,
  ([5, 1, 0, 8, 0, 5, 1, 6, 5, 1, 0, 8, 0, 5, 6, 1], [6, 5, 1, 0, 8, 0, 5, 1], [.commute 6,
    .commute 7, .square 8, .braid 2, .commute 4, .commute 5, .commute 6, .braid 7, .square 9,
    .commute 0, .commute 1, .braid 2, .commute 4, .braid 5, .commute 7, .square 8, .braid 3,
    .commute 5, .commute 6, .square 7, .commute 2, .braid 3, .commute 5, .commute 1, .commute 2,
    .braid 3, .commute 0, .commute 1])
,
  ([6, 5, 1, 0, 8, 0, 5, 1, 5, 1, 0, 8, 0, 5, 1], [6], [.commute 6, .square 7, .square 6,
    .square 5, .square 4, .square 3, .commute 1, .square 2, .square 1])
,
  ([5, 1, 0, 8, 0, 5, 1, 5, 1, 0, 8, 0, 5, 1], [], [.commute 5, .square 6, .square 5, .square 4,
    .square 3, .square 2, .commute 0, .square 1, .square 0])
,
  ([0, 8, 0, 1, 2, 1], [0, 8, 0, 1, 2, 1], [])
,
  ([0, 8, 0, 1, 0, 5, 0, 1], [0, 8, 1, 0, 5, 0, 1, 0], [.braid 2, .commute 4, .braid 5])
,
  ([0, 8, 1, 0, 5, 0, 1, 0, 2, 1, 0, 8, 0, 1, 2], [0, 8, 1, 0, 5, 2, 1, 0, 8, 0, 1, 2, 0, 1, 0],
    [.commute 7, .braid 8, .commute 10, .braid 11, .commute 13, .braid 6, .commute 8, .commute
    9, .commute 10, .braid 11, .commute 5, .braid 6, .commute 8, .braid 9, .commute 11])
,
  ([0, 8, 1, 0, 5, 2, 1, 0, 8, 0, 1, 2, 0, 1, 0, 2, 1, 0, 8, 0, 1, 2], [0, 8, 1, 0, 5, 0, 1, 0],
    [.commute 11, .braid 9, .braid 11, .commute 13, .square 14, .commute 10, .braid 11, .square
    13, .square 12, .commute 8, .commute 9, .commute 10, .square 11, .braid 6, .commute 8,
    .commute 5, .braid 6, .braid 8, .square 10, .square 9, .commute 7, .square 8])
,
  ([0, 8, 1, 0, 5, 0, 1, 0, 6, 5, 1, 0, 8, 0, 5, 6, 1], [8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 5, 0, 1],
    [.braid 5, .commute 7, .commute 8, .square 9, .commute 4, .braid 2, .braid 4, .braid 6,
    .commute 8, .commute 9, .commute 10, .commute 5, .braid 6, .commute 8, .braid 0, .commute 2,
    .commute 3, .commute 4, .commute 5, .braid 6, .braid 8, .braid 10, .square 12, .commute 9,
    .braid 3, .commute 5, .commute 6, .braid 7, .braid 9, .commute 2, .commute 3, .commute 1])
,
  ([8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 5, 0, 1, 0, 8, 0], [1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 6, 5, 0, 1],
    [.commute 6, .commute 7, .commute 3, .braid 4, .commute 6, .braid 7, .commute 9, .commute 1,
    .commute 2, .commute 3, .braid 4, .commute 6, .braid 7, .braid 9, .commute 11, .braid 12,
    .square 14, .braid 10, .commute 12, .commute 9, .braid 10, .commute 8, .braid 1, .commute 3,
    .commute 4, .commute 5, .braid 6, .braid 8, .commute 10, .commute 4, .commute 5, .commute 6,
    .commute 3, .commute 0, .braid 1, .braid 3, .commute 5, .braid 6, .commute 8, .commute 9,
    .commute 5, .commute 6, .commute 4])
,
  ([1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 6, 5, 0, 1, 1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 1], [1, 0, 8,
    5, 6, 0, 5, 2, 1, 0, 8, 6, 5, 0, 1], [.square 13, .square 12, .square 11, .commute 9,
    .commute 10, .commute 11, .braid 12, .square 14, .commute 8, .commute 9, .braid 10, .commute
    12, .commute 13, .square 14, .commute 7, .braid 8, .commute 10, .commute 11, .commute 12,
    .square 13, .commute 7, .commute 8, .commute 9, .commute 10])
,
  ([1, 0, 8, 5, 6, 0, 5, 2, 1, 0, 8, 6, 5, 0, 1, 5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1], [1, 2, 8, 0, 5, 0, 1, 6, 8, 0, 5, 6, 0, 8, 1, 0, 5, 2,
    1, 0, 8, 5, 6, 2, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1], [.commute 10, .commute
    11, .commute 9, .commute 6, .commute 7, .commute 4, .commute 5, .commute 6, .braid 7, .braid
    9, .braid 11, .commute 13, .commute 14, .commute 15, .commute 6, .commute 7, .commute 4,
    .commute 3, .braid 4, .commute 6, .braid 7, .commute 9, .commute 10, .braid 11, .commute 9,
    .commute 2, .commute 1, .braid 2, .commute 4, .commute 5, .commute 6, .braid 7, .braid 9,
    .commute 11, .braid 12, .commute 14, .braid 15, .commute 17, .commute 18, .commute 19,
    .braid 20, .square 22, .braid 10, .commute 12, .commute 13, .commute 14, .commute 9, .braid
    10, .commute 12, .commute 8, .braid 6, .braid 8, .commute 10, .commute 11, .braid 12, .braid
    14, .commute 16, .braid 17, .commute 19, .commute 20, .commute 21, .commute 22, .commute 5,
    .commute 6])
,
  ([1, 2, 8, 0, 5, 0, 1, 6, 8, 0, 5, 6, 0, 8, 1, 0, 5, 2, 1, 0, 8, 5, 6, 2, 1, 0, 5, 2, 1, 0, 8,
    1, 0, 5, 6, 0, 5, 0, 1, 2, 1], [1, 2, 8, 5, 0, 1, 6, 5, 0, 8, 2, 1, 0, 1, 5, 6, 0, 1, 2, 5,
    0, 1, 8, 0, 5, 1, 8, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1], [.commute 7, .commute 8, .braid 9,
    .braid 3, .commute 5, .commute 6, .braid 7, .commute 9, .braid 10, .commute 12, .commute 13,
    .braid 14, .commute 16, .braid 17, .commute 19, .commute 20, .commute 21, .braid 22,
    .commute 24, .commute 25, .square 26, .commute 19, .commute 20, .commute 21, .commute 22,
    .commute 15, .commute 16, .braid 17, .commute 19, .commute 20, .commute 14, .braid 15,
    .commute 17, .commute 18, .braid 13, .commute 15, .commute 16, .commute 17, .braid 18,
    .braid 20, .braid 22, .commute 24, .commute 25, .braid 8, .commute 10, .commute 11, .commute
    12, .commute 13, .commute 14, .braid 15, .commute 17, .commute 18, .commute 7, .braid 8,
    .commute 10, .commute 11, .commute 12, .braid 13, .commute 15, .commute 6, .commute 7,
    .braid 8, .commute 10, .braid 11])
,
  ([1, 2, 8, 5, 0, 1, 6, 5, 0, 8, 2, 1, 0, 1, 5, 6, 0, 1, 2, 5, 0, 1, 8, 0, 5, 1, 8, 0, 8, 1, 0,
    5, 6, 0, 5, 0, 1, 2, 1], [8, 5, 6, 0, 1, 2, 5, 0, 1, 0, 8, 0, 5, 0, 1, 2, 6, 5, 0, 1, 5, 0,
    8, 5, 0, 1, 6, 0, 5, 0, 1, 2, 1], [.commute 13, .commute 14, .braid 15, .commute 17, .braid
    18, .commute 20, .commute 21, .braid 22, .commute 20, .commute 9, .commute 10, .commute 8,
    .commute 5, .commute 6, .commute 1, .commute 2, .commute 3, .commute 4, .commute 5, .braid
    6, .braid 8, .braid 10, .commute 12, .commute 13, .commute 5, .commute 6, .commute 3,
    .commute 0, .commute 1, .commute 2, .braid 3, .commute 5, .braid 6, .commute 8, .commute 9,
    .braid 10, .commute 12, .braid 13, .commute 15, .commute 16, .commute 17, .braid 18, .braid
    20, .commute 22, .braid 23, .braid 25, .square 27, .commute 24, .braid 25, .square 27,
    .braid 21, .commute 23, .commute 19, .commute 20, .braid 21, .braid 23, .commute 25, .square
    26, .commute 12, .commute 13, .commute 14, .commute 15, .commute 11, .braid 9])
,
  ([8, 5, 6, 0, 1, 2, 5, 0, 1, 0, 8, 0, 5, 0, 1, 2, 6, 5, 0, 1, 5, 0, 8, 5, 0, 1, 6, 0, 5, 0, 1,
    2, 1], [5, 6, 8, 2, 1, 0, 8, 5, 0, 1, 2, 0, 5, 6, 8, 0, 5, 1, 0, 8, 6, 5, 0, 1, 5, 0, 1, 2,
    1], [.braid 11, .commute 13, .commute 14, .braid 15, .commute 17, .commute 18, .braid 7,
    .commute 9, .commute 10, .braid 11, .commute 13, .commute 14, .braid 15, .commute 17, .braid
    18, .commute 20, .commute 21, .commute 5, .commute 4, .braid 5, .commute 7, .commute 8,
    .commute 9, .commute 10, .braid 11, .commute 13, .commute 14, .braid 15, .commute 17, .braid
    18, .commute 20, .braid 21, .commute 23, .commute 24, .square 25, .commute 16, .commute 17,
    .commute 15, .braid 13, .braid 15, .braid 17, .commute 19, .commute 20, .commute 21, .braid
    22, .square 24, .commute 8, .commute 4, .commute 5, .braid 6, .braid 8, .commute 10,
    .commute 11, .commute 12, .commute 13, .commute 3, .braid 4, .commute 6, .commute 7, .braid
    8, .commute 10, .commute 6, .commute 0, .commute 1])
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
