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
/-- Exact bounded chunks of literal E8 square, commutation and braid moves, block 1. -/
def y431AuxE8RewriteData01 : Fin 64 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
![
  ([2, 1, 5, 0, 8, 0, 1, 2, 5], [5, 2, 1, 0, 8, 0, 5, 1, 2], [.commute 7, .commute 6, .commute
    1, .commute 0])
,
  ([2, 6, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [6,
    5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [.commute 0,
    .commute 1, .square 2])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1, 6, 5, 1,
    0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [5, 6, 0, 5, 8, 0,
    2, 1, 2, 0, 1, 8, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2,
    1, 0, 5, 1, 2, 0], [.commute 21, .braid 19, .braid 21, .commute 23, .commute 24, .commute
    25, .commute 26, .square 27, .commute 20, .braid 21, .commute 23, .commute 24, .commute 25,
    .square 26, .square 25, .commute 18, .commute 19, .commute 20, .braid 21, .commute 23,
    .square 24, .commute 17, .commute 18, .commute 19, .commute 13, .commute 14, .braid 15,
    .commute 17, .commute 10, .commute 11, .commute 12, .commute 13, .commute 14, .braid 15,
    .braid 17, .braid 19, .commute 21, .commute 22, .square 23, .commute 11, .braid 12, .commute
    14, .commute 15, .commute 9, .commute 10, .commute 11, .braid 12, .commute 14, .braid 15,
    .commute 17, .commute 18, .braid 19, .commute 21, .square 22, .commute 17, .braid 6,
    .commute 8, .commute 9, .commute 10, .commute 5, .braid 6, .commute 8, .commute 4, .commute
    5])
,
  ([5, 6, 0, 5, 8, 0, 2, 1, 2, 0, 1, 8, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 5, 6, 1, 0, 5, 2, 1, 0, 8,
    2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [5, 6, 5, 0, 1, 8, 2, 0, 5, 1, 0, 8, 6, 5, 0, 1, 0, 2,
    5, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [.braid 6, .braid 8, .braid 10,
    .commute 12, .commute 13, .commute 14, .braid 15, .braid 17, .commute 19, .commute 20,
    .square 21, .commute 13, .commute 14, .commute 15, .commute 12, .commute 9, .braid 10,
    .braid 12, .commute 14, .braid 15, .commute 17, .commute 18, .commute 19, .square 20,
    .commute 7, .commute 8, .commute 9, .braid 5, .commute 7, .commute 4, .braid 5, .braid 7,
    .braid 9, .commute 11, .commute 12, .commute 13, .commute 14, .commute 15, .commute 16,
    .braid 17, .square 19, .commute 6, .braid 4, .braid 6, .commute 8, .commute 9, .commute 10,
    .braid 11, .commute 13, .braid 14, .commute 16, .commute 17, .commute 9, .commute 7, .braid
    2, .commute 4, .commute 5, .commute 6, .braid 7, .braid 9, .commute 11, .commute 12,
    .commute 13, .braid 14])
,
  ([5, 6, 5, 0, 1, 8, 2, 0, 5, 1, 0, 8, 6, 5, 0, 1, 0, 2, 5, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2,
    1, 0, 5, 1, 2, 0], [5, 6, 5, 1, 0, 8, 0, 5, 1, 0, 2, 1, 6, 5, 0, 1, 0, 5, 1, 2, 0],
    [.commute 16, .braid 17, .square 19, .commute 16, .commute 17, .square 18, .commute 15,
    .braid 13, .braid 15, .square 17, .square 16, .commute 11, .commute 10, .braid 11, .commute
    13, .commute 14, .square 15, .commute 13, .commute 14, .commute 15, .commute 9, .commute 10,
    .braid 11, .commute 13, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .braid
    11, .braid 13, .braid 15, .square 17, .commute 8, .commute 9, .commute 10, .commute 11,
    .commute 12, .commute 13, .commute 7, .braid 5, .braid 7, .commute 9, .commute 10, .braid 3,
    .commute 5, .commute 6, .braid 7, .commute 9, .braid 10, .commute 12, .braid 13, .commute
    15, .square 16, .commute 9, .commute 10, .commute 8, .braid 6, .braid 8, .braid 10, .commute
    12, .commute 13, .commute 14, .square 15])
,
  ([5, 6, 5, 1, 0, 8, 0, 5, 1, 0, 2, 1, 6, 5, 0, 1, 0, 5, 1, 2, 0], [6, 5, 1, 0, 8, 0, 5, 6, 1],
    [.commute 11, .commute 12, .commute 9, .commute 10, .commute 7, .commute 8, .braid 0,
    .commute 2, .commute 3, .commute 4, .commute 5, .commute 6, .commute 7, .braid 8, .braid 10,
    .braid 12, .square 14, .square 13, .commute 11, .square 12, .square 11, .commute 7, .commute
    8, .commute 9, .square 10, .square 9, .commute 6, .commute 7])
,
  ([3, 6, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [6,
    5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0],
    [.commute 0, .commute 1])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1, 6, 5, 3,
    2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [5, 6, 0, 5,
    2, 1, 0, 8, 6, 2, 1, 0, 1, 5, 6, 2, 1, 0, 5, 8, 0, 1, 2, 0, 1, 3, 2, 1, 0, 8, 5, 6, 1, 0, 5,
    2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [.commute 21, .braid 19, .braid 21,
    .commute 23, .commute 24, .commute 25, .commute 26, .square 27, .commute 20, .braid 21,
    .commute 23, .commute 24, .commute 25, .square 26, .commute 17, .commute 18, .commute 19,
    .commute 20, .braid 15, .commute 13, .commute 12, .braid 13, .commute 15, .braid 16,
    .commute 18, .commute 10, .commute 11, .commute 9, .commute 10, .braid 11, .commute 13,
    .commute 14, .commute 15, .braid 16, .braid 18, .braid 20, .commute 22, .commute 23,
    .commute 24, .commute 25, .commute 26, .commute 27, .braid 28, .square 30, .braid 13,
    .commute 15, .commute 16, .commute 12, .braid 13, .commute 15, .braid 16, .commute 18,
    .commute 19, .braid 20, .commute 22, .commute 10, .commute 9, .braid 10, .commute 12,
    .commute 13, .commute 14, .commute 8, .commute 9, .braid 10])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 6, 2, 1, 0, 1, 5, 6, 2, 1, 0, 5, 8, 0, 1, 2, 0, 1, 3, 2, 1, 0, 8, 5,
    6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [5, 6, 0, 5, 2, 6, 0, 1, 0, 2,
    8, 0, 1, 5, 6, 0, 8, 5, 0, 1, 2, 0, 3, 2, 1, 0, 5, 6, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0,
    5, 1, 2, 0], [.commute 12, .commute 13, .braid 14, .commute 16, .commute 17, .commute 18,
    .commute 19, .braid 20, .braid 22, .commute 24, .commute 25, .braid 26, .commute 28,
    .commute 29, .commute 30, .square 31, .commute 23, .braid 24, .commute 26, .commute 27,
    .commute 28, .commute 29, .commute 30, .commute 31, .square 32, .commute 13, .commute 14,
    .commute 15, .commute 12, .commute 13, .commute 11, .braid 9, .braid 11, .braid 13, .braid
    15, .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .commute 22, .commute
    23, .commute 24, .commute 25, .commute 26, .braid 27, .braid 29, .braid 31, .commute 33,
    .braid 34, .commute 36, .commute 37, .commute 38, .square 39, .commute 26, .commute 27,
    .commute 16, .commute 14, .commute 7, .commute 8, .commute 9, .commute 6, .commute 5, .braid
    6])
,
  ([5, 6, 0, 5, 2, 6, 0, 1, 0, 2, 8, 0, 1, 5, 6, 0, 8, 5, 0, 1, 2, 0, 3, 2, 1, 0, 5, 6, 8, 0, 5,
    1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 1, 2, 0], [2, 0, 5, 6, 5, 0, 1, 2, 8, 0, 5, 6, 1, 0, 8, 5,
    0, 1, 2, 5, 3, 2, 1, 0, 8, 5, 0, 1, 6, 5, 0, 8, 2, 1, 0, 5, 6, 5, 1, 2, 0], [.commute 8,
    .braid 9, .commute 11, .commute 12, .commute 13, .braid 14, .braid 16, .commute 18, .commute
    19, .commute 11, .commute 12, .commute 3, .commute 1, .commute 2, .braid 3, .commute 1,
    .commute 0, .braid 1, .commute 3, .braid 4, .commute 6, .commute 7, .commute 8, .braid 9,
    .commute 11, .braid 12, .commute 14, .commute 15, .braid 16, .commute 18, .braid 19,
    .commute 21, .commute 22, .commute 23, .braid 24, .commute 26, .braid 27, .commute 29,
    .commute 30, .braid 31, .commute 33, .braid 34, .commute 36, .commute 37, .square 38,
    .commute 29, .commute 20, .commute 21, .braid 22, .commute 24, .commute 25, .commute 26,
    .braid 27, .braid 29, .commute 31, .commute 32, .commute 33, .braid 34, .commute 36, .square
    37, .commute 25, .commute 26, .commute 27, .commute 24])
,
  ([2, 0, 5, 6, 5, 0, 1, 2, 8, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 5, 3, 2, 1, 0, 8, 5, 0, 1, 6, 5, 0,
    8, 2, 1, 0, 5, 6, 5, 1, 2, 0], [0, 6, 5, 0, 1, 2, 8, 0, 1, 5, 0, 6, 5, 8, 0, 1, 2, 3, 6, 2,
    1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 2, 0], [.commute 14, .braid 2, .commute 4,
    .commute 5, .commute 6, .commute 7, .commute 8, .braid 9, .commute 11, .braid 12, .braid 14,
    .commute 16, .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .braid 22,
    .braid 24, .commute 26, .braid 27, .commute 29, .commute 30, .commute 31, .commute 32,
    .commute 33, .braid 34, .square 36, .commute 23, .commute 18, .commute 19, .commute 20,
    .braid 21, .braid 23, .commute 25, .commute 26, .commute 27, .braid 28, .commute 30, .braid
    31, .commute 33, .commute 34, .square 35, .commute 25, .commute 26, .commute 24, .commute
    22, .commute 10, .commute 11, .commute 9, .commute 0, .commute 1, .commute 2, .commute 3,
    .braid 4, .commute 6, .braid 7, .braid 9, .braid 11, .commute 13, .commute 14, .commute 15,
    .commute 16, .commute 17])
,
  ([0, 6, 5, 0, 1, 2, 8, 0, 1, 5, 0, 6, 5, 8, 0, 1, 2, 3, 6, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2,
    1, 0, 5, 6, 2, 0], [6, 5, 0, 1, 2, 8, 0, 5, 1, 0, 6, 5, 8, 3, 2, 1, 0, 1, 8, 5, 6, 0, 5, 2,
    1, 0, 8, 3, 2, 1, 0, 5, 6], [.commute 18, .commute 19, .commute 20, .commute 21, .braid 22,
    .braid 24, .braid 26, .commute 28, .braid 29, .commute 31, .commute 32, .commute 33, .square
    34, .commute 25, .commute 8, .commute 0, .braid 1, .commute 3, .commute 4, .commute 5,
    .braid 6, .braid 8, .commute 10, .commute 11, .commute 12, .braid 13, .commute 15, .commute
    16, .commute 17, .braid 18, .commute 20, .commute 21, .commute 22, .braid 23, .braid 25,
    .commute 27, .commute 28, .commute 29, .braid 30, .commute 32, .square 33, .braid 15,
    .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .commute 22, .commute 23,
    .commute 24, .commute 25, .commute 26, .commute 23, .commute 14, .braid 15, .commute 17,
    .commute 18, .commute 19, .commute 20, .commute 21, .commute 22, .commute 13, .commute 14,
    .braid 15])
,
  ([6, 5, 0, 1, 2, 8, 0, 5, 1, 0, 6, 5, 8, 3, 2, 1, 0, 1, 8, 5, 6, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0,
    5, 6], [6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6], [.commute 17, .commute 18, .commute 19, .commute 12, .commute 13, .commute
    14, .braid 15, .commute 9, .commute 8, .commute 4, .commute 5, .commute 6, .commute 7,
    .commute 3])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1, 0], [5,
    6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1, 0], [])
,
  ([0, 1, 2, 1, 0, 5, 0, 6, 5, 0, 1, 8, 0, 1, 2, 5, 0, 1, 6, 5, 0, 8, 0, 1, 2, 5, 0, 6, 5], [0,
    2, 1, 0, 6, 5, 0, 8, 6, 0, 1, 2, 5, 6, 0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0],
    [.commute 26, .commute 10, .braid 11, .commute 13, .braid 14, .commute 16, .braid 17,
    .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .braid 24, .braid 26,
    .commute 23, .commute 24, .commute 25, .commute 26, .commute 22, .commute 23, .braid 1,
    .commute 3, .commute 4, .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .commute
    10, .braid 11, .commute 13, .braid 14, .commute 16, .braid 17, .commute 19, .braid 20,
    .commute 22, .braid 23, .commute 25, .commute 12, .commute 13, .commute 11, .commute 5,
    .braid 6, .commute 8, .braid 9, .braid 11, .braid 13, .commute 15, .commute 16, .commute 17,
    .commute 18, .commute 19, .commute 20, .commute 21, .commute 14, .commute 15, .commute 12,
    .commute 13, .commute 10, .commute 11, .braid 4, .commute 6, .commute 7])
,
  ([0, 2, 1, 0, 6, 5, 0, 8, 6, 0, 1, 2, 5, 6, 0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [6,
    0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0],
    [.commute 8, .commute 9, .commute 10, .braid 11, .braid 13, .braid 15, .commute 17, .commute
    10, .commute 11, .commute 12, .commute 13, .commute 9, .commute 10, .commute 3, .braid 4,
    .commute 6, .braid 7, .commute 9, .braid 10, .commute 12, .braid 13, .commute 15, .commute
    16, .commute 2, .commute 3, .commute 1, .commute 2, .commute 0])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1, 6, 0, 5,
    2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [5, 6, 0, 5,
    2, 1, 8, 0, 5, 6, 5, 8, 2, 1, 0, 8, 1, 2, 5, 0, 1, 8, 6, 5, 0, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1,
    0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [.commute 21, .braid 19, .braid 21, .commute 23, .commute 24,
    .commute 25, .commute 26, .square 27, .braid 24, .commute 26, .commute 27, .square 28,
    .commute 23, .braid 24, .commute 26, .square 27, .commute 22, .commute 23, .braid 24,
    .square 26, .commute 17, .commute 18, .braid 15, .commute 13, .commute 12, .braid 13,
    .commute 15, .braid 16, .braid 18, .commute 20, .commute 21, .commute 22, .commute 19,
    .commute 20, .braid 14, .commute 16, .commute 17, .commute 18, .commute 12, .commute 11,
    .braid 12, .commute 14, .commute 15, .commute 16, .commute 17, .braid 18, .braid 20, .braid
    22, .commute 24, .square 25, .braid 23, .square 25, .commute 17, .commute 18, .commute 19,
    .commute 20, .commute 21, .commute 15, .commute 16, .commute 17, .braid 6, .commute 8,
    .commute 9, .commute 10])
,
  ([5, 6, 0, 5, 2, 1, 8, 0, 5, 6, 5, 8, 2, 1, 0, 8, 1, 2, 5, 0, 1, 8, 6, 5, 0, 6, 1, 0, 5, 2, 1,
    0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [5, 0, 2, 1, 5, 6, 2, 0, 8, 5, 0, 1, 2, 6, 5, 0,
    8, 5, 6, 0, 5, 0, 1, 0, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [.commute
    11, .commute 12, .braid 13, .commute 3, .commute 4, .commute 5, .braid 6, .commute 8,
    .commute 1, .commute 2, .commute 3, .commute 4, .commute 5, .braid 6, .braid 8, .commute 10,
    .braid 11, .commute 13, .braid 14, .commute 16, .braid 17, .commute 19, .commute 20, .braid
    21, .commute 23, .square 24, .commute 19, .commute 20, .commute 21, .braid 12, .commute 14,
    .commute 15, .commute 16, .braid 17, .commute 19, .commute 11, .braid 12, .commute 14,
    .braid 15, .commute 17, .commute 7, .braid 5, .braid 7, .commute 9, .commute 10, .commute
    11, .commute 12, .commute 13, .commute 8, .commute 9, .commute 6, .commute 7, .commute 4,
    .commute 5, .commute 6, .braid 7, .braid 9, .commute 11, .commute 12, .braid 13, .commute
    15, .commute 16, .braid 17, .braid 19])
,
  ([5, 0, 2, 1, 5, 6, 2, 0, 8, 5, 0, 1, 2, 6, 5, 0, 8, 5, 6, 0, 5, 0, 1, 0, 1, 0, 5, 2, 1, 0, 8,
    2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [2, 0, 5, 1, 0, 8, 5, 2, 1, 0, 2, 5, 8, 1, 2, 1, 0, 5,
    1, 2, 0], [.braid 21, .square 23, .square 22, .commute 20, .square 21, .commute 12, .commute
    13, .commute 14, .commute 15, .commute 16, .commute 17, .commute 18, .braid 19, .square 21,
    .commute 11, .commute 12, .commute 10, .commute 5, .commute 6, .commute 7, .braid 8, .braid
    10, .braid 12, .commute 14, .commute 15, .commute 16, .braid 17, .commute 19, .square 20,
    .commute 14, .commute 15, .commute 11, .braid 12, .commute 14, .braid 15, .commute 17,
    .commute 18, .square 19, .square 18, .square 17, .square 16, .commute 9, .commute 10,
    .commute 11, .braid 12, .commute 14, .square 15, .commute 13, .square 14, .braid 9, .commute
    11, .commute 12, .commute 5, .commute 6, .commute 7, .commute 3, .commute 1, .commute 0,
    .braid 1, .braid 3, .commute 5, .commute 6, .braid 7, .commute 9])
,
  ([2, 0, 5, 1, 0, 8, 5, 2, 1, 0, 2, 5, 8, 1, 2, 1, 0, 5, 1, 2, 0], [1, 0, 5, 2, 1, 0, 8, 0, 5,
    1, 2, 0, 1], [.commute 10, .commute 11, .braid 12, .square 14, .commute 10, .commute 11,
    .commute 12, .commute 5, .commute 6, .commute 7, .braid 8, .commute 2, .braid 3, .commute 5,
    .braid 6, .commute 8, .braid 9, .commute 11, .braid 12, .square 14, .commute 11, .commute
    12, .commute 10, .commute 4, .commute 5, .commute 3, .commute 0, .braid 1, .braid 3, .braid
    5, .commute 7, .braid 8, .braid 10, .braid 12, .square 14, .commute 11, .commute 2, .braid
    0, .braid 2, .commute 4, .commute 5, .commute 6, .commute 7, .commute 8, .braid 9, .braid
    11, .square 13, .commute 3, .commute 2])
,
  ([1, 0, 2, 1, 5, 0, 8, 0, 1, 2, 5, 0, 1], [1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 1], [.commute
    9, .commute 8, .commute 3, .commute 2])
,
  ([1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 1, 6, 5, 1, 0, 8, 0, 5, 6, 1], [1, 0, 8, 5, 6, 0, 5, 2,
    1, 0, 8, 6, 5, 2, 0, 1], [.commute 12, .commute 13, .square 14, .commute 11, .braid 12,
    .commute 14, .braid 5, .commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .braid
    12, .braid 14, .square 16, .commute 7, .commute 8, .braid 9, .commute 11, .commute 12,
    .commute 4, .braid 5, .commute 7, .commute 8, .braid 9, .commute 11, .braid 12, .commute 14,
    .square 15, .commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12,
    .commute 6, .commute 7, .commute 3, .commute 4, .commute 5, .commute 6, .commute 4, .commute
    2])
,
  ([1, 0, 8, 5, 6, 0, 5, 2, 1, 0, 8, 6, 5, 2, 0, 1, 1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 1], [6,
    5, 1, 0, 8, 0, 5, 6, 1], [.square 15, .square 14, .commute 12, .square 13, .square 12,
    .commute 10, .commute 11, .commute 9, .commute 8, .braid 9, .braid 11, .square 13, .square
    12, .commute 6, .commute 4, .commute 5, .braid 6, .commute 4, .commute 3, .braid 4, .commute
    6, .braid 7, .commute 9, .commute 10, .square 11, .commute 9, .square 10, .commute 3,
    .commute 4, .commute 5, .commute 6, .commute 7, .commute 8, .square 9, .braid 1, .commute 3,
    .commute 4, .commute 5, .braid 6, .square 8, .braid 3, .commute 5, .commute 6, .commute 2,
    .braid 3, .commute 5, .commute 1, .commute 2, .braid 3, .commute 0, .commute 1])
,
  ([1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 1, 6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0,
    5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 6, 5, 0, 1,
    8, 0, 5, 6, 2, 3, 1, 0, 8, 2, 1, 0, 5, 6, 0, 8, 1, 2, 0, 1, 0, 5, 0, 8, 3, 2, 1, 0, 5, 6,
    1], [.braid 28, .commute 30, .commute 31, .commute 32, .commute 24, .commute 25, .commute
    26, .commute 27, .braid 28, .commute 30, .commute 26, .commute 23, .commute 24, .commute 16,
    .commute 12, .commute 13, .braid 14, .braid 16, .commute 18, .commute 19, .commute 20,
    .commute 21, .commute 22, .commute 23, .braid 24, .braid 26, .commute 28, .commute 29,
    .braid 30, .braid 32, .commute 34, .commute 35, .commute 36, .braid 37, .commute 39,
    .commute 40, .braid 41, .commute 43, .commute 44, .commute 34, .commute 35, .commute 33,
    .commute 31, .commute 23, .commute 24, .commute 21, .commute 11, .braid 12, .commute 14,
    .commute 15, .braid 16, .commute 18, .commute 19, .commute 20, .braid 21, .commute 23,
    .braid 24, .commute 26, .commute 27, .commute 28, .commute 29, .commute 30, .braid 31,
    .braid 33])
,
  ([1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 6, 5, 0, 1, 8, 0, 5, 6, 2, 3, 1, 0, 8, 2, 1, 0, 5, 6, 0, 8,
    1, 2, 0, 1, 0, 5, 0, 8, 3, 2, 1, 0, 5, 6, 1], [1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 0, 1, 2, 3,
    8, 0, 1, 5, 0, 8, 2, 1, 0, 1, 5, 6, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 3, 2, 1, 0, 5, 6, 2, 0,
    1], [.braid 35, .commute 37, .commute 38, .commute 39, .commute 40, .braid 41, .commute 43,
    .commute 34, .commute 18, .commute 19, .commute 20, .commute 21, .commute 22, .commute 23,
    .commute 24, .commute 25, .braid 26, .commute 17, .commute 18, .commute 19, .commute 16,
    .commute 17, .commute 14, .commute 10, .commute 11, .commute 12, .commute 13, .braid 14,
    .commute 16, .braid 17, .braid 19, .commute 21, .commute 22, .commute 23, .braid 24,
    .commute 26, .braid 27, .commute 29, .commute 30, .commute 31, .braid 32, .braid 34,
    .commute 36, .commute 37, .braid 38, .commute 40, .commute 41, .commute 42, .commute 29,
    .commute 30, .commute 13, .commute 14, .commute 15, .commute 9, .commute 10, .braid 11,
    .commute 13, .commute 14, .braid 15, .commute 17, .commute 18, .braid 19, .commute 21,
    .braid 22])
,
  ([1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 0, 1, 2, 3, 8, 0, 1, 5, 0, 8, 2, 1, 0, 1, 5, 6, 5, 0, 1, 2,
    8, 0, 5, 1, 0, 8, 3, 2, 1, 0, 5, 6, 2, 0, 1], [1, 0, 5, 2, 1, 0, 8, 0, 6, 5, 0, 1, 2, 3, 8,
    0, 1, 5, 6, 2, 0, 5, 8, 0, 1, 2, 0, 8, 5, 6, 0, 1, 5, 0, 8, 3, 2, 1, 0, 5, 6, 5, 1, 2, 0,
    1], [.commute 24, .commute 25, .commute 26, .braid 27, .commute 29, .braid 30, .commute 32,
    .commute 33, .braid 34, .commute 36, .commute 37, .braid 38, .commute 40, .commute 41,
    .braid 24, .commute 26, .commute 27, .commute 28, .commute 29, .commute 30, .commute 23,
    .braid 24, .commute 26, .commute 27, .commute 28, .commute 22, .commute 23, .braid 24,
    .commute 26, .commute 20, .commute 21, .commute 22, .commute 19, .commute 20, .commute 18,
    .braid 8, .commute 10, .commute 11, .commute 12, .commute 13, .commute 14, .commute 15,
    .commute 16, .commute 17, .braid 18, .braid 20, .braid 22, .commute 24, .commute 25, .braid
    26, .braid 28, .braid 30, .commute 32, .commute 33, .commute 34, .commute 35, .commute 36,
    .commute 37, .commute 38, .braid 39, .commute 31, .commute 29, .commute 17, .commute 18])
,
  ([1, 0, 5, 2, 1, 0, 8, 0, 6, 5, 0, 1, 2, 3, 8, 0, 1, 5, 6, 2, 0, 5, 8, 0, 1, 2, 0, 8, 5, 6, 0,
    1, 5, 0, 8, 3, 2, 1, 0, 5, 6, 5, 1, 2, 0, 1], [1, 0, 5, 2, 1, 0, 6, 5, 0, 8, 1, 0, 5, 6, 2,
    1, 0, 5, 8, 2, 0, 3, 2, 1, 0, 8, 5, 6, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 5, 1, 2, 0,
    1], [.commute 19, .commute 20, .commute 21, .commute 22, .braid 23, .commute 16, .commute
    17, .commute 7, .braid 8, .commute 10, .commute 11, .commute 12, .commute 13, .braid 14,
    .commute 16, .braid 17, .commute 19, .commute 20, .braid 21, .commute 23, .braid 24,
    .commute 26, .commute 27, .commute 28, .braid 29, .braid 31, .commute 33, .commute 34,
    .commute 35, .commute 36, .braid 37, .commute 39, .commute 30, .braid 22, .commute 24,
    .commute 25, .commute 26, .commute 27, .commute 28, .commute 29, .commute 12, .commute 13,
    .commute 14, .commute 15, .commute 16, .commute 17, .commute 18, .commute 19, .commute 20,
    .commute 11, .commute 12, .commute 13, .commute 14, .commute 10, .commute 6, .commute 7,
    .braid 8, .braid 10, .commute 12, .commute 13, .braid 14, .commute 16, .commute 17, .commute
    18])
,
  ([1, 0, 5, 2, 1, 0, 6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 8, 2, 0, 3, 2, 1, 0, 8, 5, 6, 0, 5, 2,
    1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 5, 1, 2, 0, 1], [6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0,
    5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 5, 1, 2, 0,
    1], [.commute 19, .braid 20, .commute 22, .commute 23, .commute 24, .commute 25, .commute
    26, .commute 27, .commute 28, .commute 19, .commute 20, .braid 21, .commute 23, .commute 24,
    .commute 25, .commute 5, .braid 6, .commute 8, .commute 9, .braid 10, .commute 12, .commute
    13, .braid 14, .commute 16, .commute 17, .commute 18, .braid 19, .commute 21, .commute 22,
    .commute 23, .commute 24, .commute 17, .commute 18, .commute 19, .braid 20, .commute 2,
    .commute 3, .braid 4, .commute 6, .commute 7, .commute 8, .commute 9, .braid 10, .commute
    12, .commute 13, .braid 14, .commute 16, .commute 17, .braid 18, .commute 20, .commute 3,
    .commute 4, .commute 2, .commute 3, .commute 1, .commute 0])
,
  ([6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2,
    1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 5, 1, 2, 0, 1, 1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 1], [6, 1,
    0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 8, 0, 1, 2, 3, 8, 5, 0, 1, 2, 6, 5, 0, 8,
    1, 0, 5, 6, 1, 2, 0, 1], [.square 45, .square 44, .commute 41, .commute 42, .square 43,
    .square 42, .square 41, .square 40, .commute 33, .commute 34, .commute 35, .commute 32,
    .commute 33, .commute 31, .braid 29, .braid 31, .braid 33, .braid 35, .commute 37, .commute
    38, .square 39, .commute 28, .commute 29, .commute 30, .commute 31, .commute 27, .commute
    28, .braid 25, .commute 27, .braid 28, .commute 30, .braid 31, .commute 33, .commute 34,
    .braid 35, .commute 37, .square 38, .commute 24, .commute 25, .commute 26, .commute 27,
    .commute 28, .commute 29, .commute 23, .commute 24, .commute 25, .braid 21, .commute 23,
    .commute 24, .braid 25, .commute 27, .commute 28, .braid 29, .commute 31, .commute 32,
    .commute 33, .commute 34, .braid 35, .square 37, .commute 32, .braid 19, .commute 21,
    .commute 22, .commute 23])
,
  ([6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 8, 0, 1, 2, 3, 8, 5, 0, 1, 2, 6, 5,
    0, 8, 1, 0, 5, 6, 1, 2, 0, 1], [6, 1, 0, 5, 0, 8, 1, 2, 0, 1, 3, 2, 5, 0, 8, 6, 5, 6, 0, 1,
    2, 3, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 2, 0, 1], [.commute 24, .commute 18, .braid
    19, .commute 21, .commute 22, .commute 15, .commute 16, .commute 17, .commute 14, .commute
    15, .commute 7, .braid 5, .braid 7, .commute 9, .commute 10, .commute 11, .commute 12,
    .commute 13, .commute 14, .braid 15, .braid 17, .commute 19, .commute 20, .commute 21,
    .braid 22, .braid 24, .commute 26, .commute 27, .commute 28, .commute 29, .braid 30, .braid
    32, .commute 34, .commute 35, .square 36, .commute 27, .commute 28, .commute 29, .commute
    30, .commute 26, .commute 27, .commute 25, .commute 23, .commute 10, .commute 11, .commute
    12, .commute 13, .commute 14, .commute 15, .commute 9, .commute 10, .commute 11, .commute
    12, .commute 8, .commute 6, .commute 4, .commute 5, .braid 6, .braid 8, .commute 10,
    .commute 11, .braid 12, .commute 14, .braid 15])
,
  ([6, 1, 0, 5, 0, 8, 1, 2, 0, 1, 3, 2, 5, 0, 8, 6, 5, 6, 0, 1, 2, 3, 0, 8, 5, 6, 0, 5, 1, 0, 8,
    2, 1, 0, 5, 6, 2, 0, 1], [6, 5, 0, 1, 2, 3, 8, 0, 5, 1, 8, 0, 8, 6, 5, 0, 1, 2, 3, 1, 0, 5,
    6, 8, 0, 1, 5, 0, 8, 2, 1, 0, 5, 6, 1], [.commute 17, .commute 18, .commute 19, .commute 20,
    .commute 21, .commute 22, .braid 23, .braid 25, .braid 27, .commute 29, .braid 30, .commute
    32, .commute 33, .commute 34, .square 35, .commute 26, .commute 11, .commute 12, .commute
    13, .commute 14, .commute 15, .commute 16, .braid 17, .commute 19, .commute 9, .commute 10,
    .commute 8, .braid 2, .commute 4, .commute 5, .commute 6, .commute 7, .braid 8, .braid 10,
    .commute 12, .commute 13, .commute 14, .braid 15, .commute 17, .commute 18, .braid 19,
    .commute 21, .commute 22, .commute 23, .braid 24, .braid 26, .commute 28, .commute 29,
    .commute 30, .braid 31, .commute 33, .square 34, .commute 21, .commute 22, .commute 4,
    .commute 5, .commute 6, .commute 1, .braid 2, .commute 4, .commute 5, .braid 6, .commute 8,
    .commute 9])
,
  ([6, 5, 0, 1, 2, 3, 8, 0, 5, 1, 8, 0, 8, 6, 5, 0, 1, 2, 3, 1, 0, 5, 6, 8, 0, 1, 5, 0, 8, 2, 1,
    0, 5, 6, 1], [6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0,
    8, 3, 2, 1, 0, 5, 6], [.braid 10, .commute 12, .braid 13, .commute 15, .commute 16, .commute
    17, .commute 18, .braid 19, .commute 21, .braid 22, .commute 24, .commute 25, .braid 26,
    .commute 28, .braid 29, .commute 31, .commute 32, .square 33, .commute 17, .commute 18,
    .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25,
    .commute 26, .commute 23, .braid 15, .commute 17, .commute 18, .commute 19, .commute 20,
    .commute 21, .commute 22, .commute 14, .braid 15, .commute 17, .commute 18, .commute 19,
    .commute 18, .commute 17, .commute 11, .commute 12, .commute 13, .commute 14, .braid 15,
    .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .commute 11,
    .commute 9, .commute 8, .commute 4, .commute 5, .commute 6, .commute 7, .commute 3])
,
  ([6, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0, 1, 0, 5,
    2, 1, 0, 8, 0, 5, 1, 2, 0, 1], [6, 2, 1, 8, 0, 5, 6, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5, 1, 6, 0,
    1, 8, 0, 5, 2, 0, 8, 1, 0, 5, 2, 1, 2, 0, 1], [.commute 24, .commute 25, .braid 22, .commute
    24, .braid 25, .commute 27, .commute 21, .braid 22, .commute 24, .braid 25, .braid 27,
    .square 29, .commute 26, .braid 24, .braid 26, .commute 23, .commute 24, .braid 21, .commute
    23, .braid 24, .commute 26, .braid 27, .square 29, .braid 25, .commute 27, .square 28,
    .commute 27, .commute 28, .commute 29, .commute 26, .commute 15, .commute 16, .commute 14,
    .braid 12, .braid 14, .braid 16, .commute 18, .commute 19, .commute 20, .commute 11,
    .commute 12, .braid 9, .commute 11, .braid 12, .commute 14, .commute 15, .braid 16, .commute
    18, .commute 14, .braid 4, .commute 6, .commute 7, .commute 1, .commute 2, .commute 3,
    .braid 4, .commute 6, .braid 7, .commute 9, .commute 10, .commute 11, .braid 12, .braid 14,
    .commute 16])
,
  ([6, 2, 1, 8, 0, 5, 6, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5, 1, 6, 0, 1, 8, 0, 5, 2, 0, 8, 1, 0, 5, 2,
    1, 2, 0, 1], [6, 2, 1, 0, 8, 5, 0, 1, 2, 6, 5, 0, 8, 5, 6, 0, 1, 5, 0, 8, 5, 6, 2, 1, 0, 5,
    1, 2, 0], [.commute 17, .braid 18, .braid 20, .commute 22, .commute 23, .braid 24, .braid
    26, .commute 28, .braid 29, .square 31, .commute 22, .commute 21, .braid 22, .commute 24,
    .commute 25, .braid 26, .commute 28, .commute 20, .commute 21, .braid 22, .braid 24,
    .commute 26, .commute 20, .commute 21, .commute 22, .commute 19, .commute 6, .commute 7,
    .commute 8, .commute 9, .commute 5, .braid 3, .braid 5, .commute 7, .commute 8, .braid 9,
    .commute 11, .commute 12, .commute 13, .commute 14, .braid 15, .braid 17, .braid 19,
    .commute 21, .braid 22, .commute 24, .commute 25, .braid 26, .braid 28, .square 30, .square
    29, .commute 16, .braid 14, .braid 16, .commute 18, .commute 19, .commute 20, .commute 17,
    .commute 15, .commute 13, .commute 14, .braid 15, .braid 17, .commute 19])
,
  ([6, 2, 1, 0, 8, 5, 0, 1, 2, 6, 5, 0, 8, 5, 6, 0, 1, 5, 0, 8, 5, 6, 2, 1, 0, 5, 1, 2, 0], [6,
    0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0],
    [.commute 12, .commute 13, .braid 10, .commute 12, .braid 13, .commute 15, .commute 16,
    .braid 17, .commute 15, .commute 9, .braid 10, .commute 12, .braid 13, .braid 15, .commute
    17, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .braid 6,
    .commute 8, .commute 9, .commute 10, .commute 5, .braid 6, .commute 8, .commute 4, .braid 2,
    .braid 4, .commute 6, .commute 7, .braid 8, .braid 10, .commute 12, .braid 13, .commute 15,
    .commute 16, .commute 7, .commute 8, .braid 5, .commute 7, .commute 4, .braid 5, .commute 3,
    .commute 1, .commute 2])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0],
    [5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0],
    [])
,
  ([0, 2, 1, 5, 0, 1, 2, 6, 5, 0, 1, 2, 8, 0, 1, 2, 5, 0, 1, 6, 5, 0, 8, 0, 1, 2, 5, 0, 6], [0,
    2, 5, 0, 1, 6, 5, 0, 8, 0, 1, 2, 5, 0, 6, 1, 5, 0, 8, 0, 5, 6, 0, 5, 0, 1, 2, 1, 0],
    [.commute 27, .commute 15, .commute 16, .commute 14, .commute 2, .braid 3, .commute 5,
    .commute 6, .braid 7, .commute 9, .commute 10, .commute 11, .braid 12, .braid 14, .braid 16,
    .commute 18, .commute 19, .commute 20, .commute 21, .commute 22, .braid 23, .commute 25,
    .commute 26, .commute 24, .commute 25, .commute 23, .commute 24, .commute 15, .commute 10,
    .commute 11, .commute 12, .braid 13, .braid 15, .commute 17, .braid 18, .commute 20, .braid
    21, .commute 23, .commute 12, .commute 13, .commute 9, .braid 10, .commute 12, .braid 13,
    .commute 15, .braid 16, .commute 18, .commute 19, .commute 20, .braid 21, .commute 5,
    .commute 6, .commute 7, .commute 8, .commute 9, .braid 10, .commute 12, .braid 13, .commute
    15, .braid 16, .commute 18, .braid 19, .commute 21, .commute 14])
,
  ([0, 2, 5, 0, 1, 6, 5, 0, 8, 0, 1, 2, 5, 0, 6, 1, 5, 0, 8, 0, 5, 6, 0, 5, 0, 1, 2, 1, 0], [5,
    6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1, 0],
    [.commute 15, .commute 13, .commute 0, .braid 1, .commute 3, .braid 4, .commute 6, .commute
    7, .commute 8, .commute 9, .commute 10, .braid 11, .braid 13, .braid 15, .commute 17,
    .commute 10, .commute 11, .commute 12, .commute 13, .commute 9, .commute 10, .commute 3,
    .commute 4, .commute 0, .commute 1, .commute 2, .commute 3, .commute 1])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1, 0, 5, 6,
    0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [5, 6,
    0, 5, 2, 1, 8, 0, 1, 6, 5, 0, 8, 0, 5, 6, 1, 2, 5, 0, 1, 8, 0, 5, 6, 0, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [.braid 22, .commute 24, .commute 25, .commute
    26, .braid 27, .commute 29, .square 30, .braid 20, .commute 22, .commute 23, .commute 24,
    .commute 25, .commute 26, .braid 27, .square 29, .braid 23, .commute 25, .commute 26,
    .commute 27, .square 28, .commute 22, .braid 23, .commute 25, .commute 26, .square 27,
    .commute 21, .commute 22, .braid 23, .commute 25, .square 26, .commute 17, .braid 15, .braid
    17, .commute 19, .commute 20, .commute 21, .commute 18, .commute 19, .commute 16, .commute
    17, .commute 14, .commute 15, .commute 16, .braid 17, .braid 19, .braid 21, .commute 23,
    .commute 24, .square 25, .braid 12, .commute 14, .commute 10, .commute 9, .braid 10,
    .commute 12, .commute 13, .braid 14, .commute 16, .commute 17, .braid 6, .commute 8,
    .commute 9, .commute 10, .braid 11])
,
  ([5, 6, 0, 5, 2, 1, 8, 0, 1, 6, 5, 0, 8, 0, 5, 6, 1, 2, 5, 0, 1, 8, 0, 5, 6, 0, 5, 6, 1, 0, 5,
    2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [2, 0, 5, 6, 8, 5, 0, 1, 0, 5, 8, 0, 1, 2,
    8, 6, 5, 0, 8, 1, 0, 5, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [.commute
    5, .braid 6, .commute 8, .braid 9, .commute 11, .braid 12, .commute 14, .commute 7, .commute
    8, .commute 6, .commute 3, .commute 4, .commute 1, .commute 2, .commute 3, .braid 4, .braid
    6, .braid 8, .commute 10, .commute 3, .commute 4, .commute 1, .commute 0, .braid 1, .commute
    3, .braid 4, .commute 6, .commute 7, .braid 8, .braid 10, .commute 12, .commute 13, .braid
    14, .commute 16, .braid 17, .commute 19, .commute 20, .braid 21, .commute 23, .square 24,
    .commute 13, .commute 14, .commute 15, .braid 11, .commute 13, .commute 14, .braid 15,
    .commute 17, .commute 18, .commute 19, .commute 20, .braid 21, .square 23, .square 22,
    .commute 18, .commute 9, .commute 10, .braid 7, .braid 5, .commute 7, .braid 8, .braid 10,
    .commute 12, .commute 13])
,
  ([2, 0, 5, 6, 8, 5, 0, 1, 0, 5, 8, 0, 1, 2, 8, 6, 5, 0, 8, 1, 0, 5, 1, 0, 5, 2, 1, 0, 8, 2, 1,
    0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [2, 0, 8, 1, 0, 5, 6, 8, 0, 5, 1, 0, 2, 0, 5, 6, 2, 1, 0, 5,
    1, 2, 0], [.commute 14, .commute 15, .braid 16, .braid 18, .commute 20, .square 21, .braid
    6, .commute 8, .commute 9, .braid 10, .commute 12, .commute 13, .braid 14, .commute 16,
    .commute 17, .braid 18, .square 20, .square 19, .commute 12, .commute 13, .commute 14,
    .commute 15, .commute 11, .commute 12, .commute 10, .commute 8, .commute 3, .commute 2,
    .braid 3, .commute 5, .commute 6, .commute 7, .braid 8, .braid 10, .braid 12, .commute 14,
    .braid 15, .commute 17, .square 18, .commute 7, .commute 8, .commute 4, .braid 5, .commute
    7, .braid 8, .commute 10, .commute 11, .braid 12, .commute 14, .braid 15, .square 17,
    .square 16, .commute 13, .commute 14, .square 15, .commute 3, .commute 4, .braid 5, .commute
    7, .braid 8, .braid 10, .braid 12, .square 14, .square 13])
,
  ([2, 0, 8, 1, 0, 5, 6, 8, 0, 5, 1, 0, 2, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [2, 1, 0, 8, 0, 1, 2],
    [.commute 11, .square 12, .commute 9, .commute 10, .square 11, .commute 6, .commute 7,
    .commute 8, .commute 9, .square 10, .square 9, .square 8, .square 7, .commute 5, .square 6,
    .commute 2, .braid 3, .braid 1, .commute 3, .braid 4, .commute 6, .square 7])
,
  ([6, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0],
    [0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0],
    [.square 0])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1, 0, 0, 5,
    2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [5, 6, 0, 5,
    2, 8, 0, 1, 6, 5, 2, 0, 8, 1, 0, 5, 1, 0, 1, 2, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0,
    5, 1, 2, 0], [.square 28, .braid 22, .commute 24, .commute 25, .commute 26, .square 27,
    .braid 24, .square 26, .square 25, .commute 23, .square 24, .commute 17, .braid 15, .braid
    17, .commute 19, .commute 20, .commute 21, .commute 22, .square 23, .commute 13, .commute
    12, .braid 13, .commute 15, .commute 16, .braid 17, .commute 19, .commute 10, .commute 11,
    .commute 9, .commute 10, .braid 11, .commute 13, .commute 14, .commute 15, .commute 16,
    .braid 17, .braid 19, .commute 21, .square 22, .commute 20, .square 21, .commute 18,
    .commute 19, .square 20, .commute 14, .braid 6, .commute 8, .commute 9, .commute 10,
    .commute 11, .braid 12, .braid 14, .commute 16, .commute 5, .braid 6, .commute 8, .commute
    9, .braid 10, .commute 12, .commute 13, .braid 14, .braid 16, .commute 8, .commute 9])
,
  ([5, 6, 0, 5, 2, 8, 0, 1, 6, 5, 2, 0, 8, 1, 0, 5, 1, 0, 1, 2, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5,
    6, 2, 1, 0, 5, 1, 2, 0], [2, 0, 5, 8, 0, 1, 6, 2, 0, 6, 2, 1, 0, 5, 1, 2, 0], [.commute 10,
    .commute 11, .commute 7, .commute 8, .commute 6, .commute 3, .commute 4, .commute 1,
    .commute 2, .commute 3, .braid 4, .braid 6, .braid 8, .commute 10, .braid 11, .commute 13,
    .commute 14, .commute 3, .commute 4, .commute 1, .commute 0, .braid 1, .commute 3, .braid 4,
    .commute 6, .commute 7, .braid 8, .commute 10, .braid 11, .commute 13, .braid 14, .commute
    16, .braid 17, .square 19, .braid 15, .commute 17, .square 18, .commute 13, .commute 12,
    .braid 13, .commute 15, .commute 16, .square 17, .square 16, .square 15, .square 14,
    .commute 9, .commute 10, .commute 11, .commute 12, .square 13, .commute 11, .square 12,
    .commute 10, .square 11, .commute 8, .commute 6, .commute 7, .braid 8, .square 10, .square
    9, .commute 3, .commute 4, .commute 5])
,
  ([2, 0, 5, 8, 0, 1, 6, 2, 0, 6, 2, 1, 0, 5, 1, 2, 0], [0, 8, 0], [.commute 6, .commute 7,
    .square 8, .commute 6, .square 7, .braid 4, .square 6, .square 5, .commute 2, .commute 3,
    .square 4, .square 3, .commute 0, .commute 1, .square 2])
,
  ([0, 1, 2, 1, 0, 1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 1], [5, 1, 0, 8, 0, 5, 0, 1, 2, 0, 1, 0],
    [.braid 3, .square 5, .commute 2, .braid 0, .braid 2, .commute 4, .square 5, .commute 3,
    .square 4, .commute 2, .commute 3, .commute 4, .commute 5, .commute 6, .braid 7, .braid 9,
    .braid 1, .commute 3, .braid 4, .commute 0])
,
  ([0, 1, 0, 2, 1, 0, 5, 0, 8, 0, 1, 5], [1, 0, 5, 2, 1, 0, 8, 0, 5, 2, 0, 1], [.commute 10,
    .braid 5, .commute 7, .braid 8, .braid 0, .braid 2, .commute 4, .commute 5, .commute 6,
    .commute 7, .commute 8, .commute 3, .commute 2])
,
  ([1, 0, 5, 2, 1, 0, 8, 0, 5, 2, 0, 1, 1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 1], [5, 1, 0, 8, 0,
    5, 1], [.square 11, .square 10, .commute 8, .square 9, .square 8, .braid 5, .commute 7,
    .commute 4, .braid 5, .braid 7, .square 9, .square 8, .commute 6, .commute 7, .square 8,
    .commute 3, .commute 4, .commute 5, .commute 6, .square 7, .braid 3, .braid 1, .commute 3,
    .braid 4, .square 6, .commute 0])
,
  ([2, 1, 0, 8, 0, 1, 2], [2, 1, 0, 8, 0, 1, 2], [])
,
  ([2, 1, 0, 8, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2,
    1, 0, 8, 3, 2, 1, 0, 5, 6], [2, 1, 0, 8, 0, 6, 5, 0, 1, 2, 8, 0, 1, 5, 6, 3, 2, 0, 8, 1, 0,
    5, 6, 0, 1, 8, 0, 5, 8, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 2], [.commute 14, .commute 15,
    .commute 16, .commute 13, .commute 14, .commute 12, .commute 6, .commute 7, .commute 8,
    .commute 9, .braid 10, .braid 12, .braid 14, .braid 16, .commute 18, .commute 19, .commute
    20, .commute 21, .commute 22, .commute 23, .braid 24, .commute 26, .braid 27, .commute 29,
    .braid 30, .commute 32, .commute 33, .braid 34, .commute 36, .commute 37, .commute 38,
    .braid 21, .commute 23, .commute 24, .commute 25, .commute 17, .commute 18, .commute 19,
    .commute 20, .braid 21, .commute 23, .commute 19, .commute 15, .commute 16, .commute 17,
    .commute 9, .commute 10, .commute 5, .commute 6, .braid 7, .commute 9, .braid 10, .commute
    12, .commute 13, .commute 14, .commute 15, .commute 16, .braid 17, .braid 19, .commute 21,
    .commute 22, .braid 23, .braid 25, .commute 27])
,
  ([2, 1, 0, 8, 0, 6, 5, 0, 1, 2, 8, 0, 1, 5, 6, 3, 2, 0, 8, 1, 0, 5, 6, 0, 1, 8, 0, 5, 8, 2, 1,
    0, 8, 3, 2, 1, 0, 5, 6, 2], [2, 1, 0, 6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 8, 3, 2, 1, 3, 0, 5,
    6, 0, 8, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 1, 2], [.commute 28, .commute 29, .braid
    30, .commute 32, .commute 33, .braid 34, .commute 36, .commute 37, .commute 27, .commute 28,
    .commute 26, .commute 24, .commute 16, .commute 17, .commute 12, .commute 13, .commute 14,
    .commute 4, .braid 5, .commute 7, .commute 8, .commute 9, .braid 10, .commute 12, .commute
    13, .braid 14, .commute 16, .braid 17, .commute 19, .commute 20, .commute 21, .commute 22,
    .commute 23, .braid 24, .braid 26, .braid 28, .commute 30, .commute 31, .commute 32,
    .commute 33, .braid 34, .commute 36, .commute 27, .commute 25, .commute 26, .commute 13,
    .commute 14, .commute 15, .commute 8, .commute 9, .commute 10, .commute 11, .commute 7,
    .commute 3, .commute 4, .braid 5, .braid 7, .commute 9, .commute 10, .braid 11, .commute 13,
    .commute 14, .braid 15, .commute 17])
,
  ([2, 1, 0, 6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 8, 3, 2, 1, 3, 0, 5, 6, 0, 8, 1, 0, 5, 2, 1, 0, 8,
    3, 2, 1, 0, 5, 6, 0, 1, 2], [6, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 1, 2], [.commute 18, .commute 19,
    .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25, .commute 2,
    .braid 3, .commute 5, .commute 6, .braid 7, .commute 9, .commute 10, .braid 11, .commute 13,
    .commute 14, .braid 15, .commute 17, .commute 18, .commute 19, .commute 20, .commute 21,
    .commute 19, .commute 20, .braid 17, .commute 19, .commute 13, .commute 14, .commute 15,
    .commute 16, .braid 17, .commute 15, .commute 14, .commute 13, .commute 1, .commute 2,
    .commute 0, .commute 1])
,
  ([6, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    3, 2, 1, 0, 5, 6, 0, 1, 2, 2, 1, 0, 8, 0, 1, 2], [6, 5, 2, 0, 1, 8, 0, 5, 6, 2, 1, 3, 2, 0,
    8, 1, 0, 5, 6, 0, 1, 2, 3, 0, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5, 6, 1, 2], [.square 39, .square
    38, .square 37, .commute 30, .commute 31, .commute 32, .commute 29, .commute 30, .commute
    28, .braid 26, .braid 28, .braid 30, .braid 32, .commute 34, .commute 35, .square 36,
    .commute 25, .commute 26, .commute 27, .commute 28, .commute 24, .commute 25, .braid 22,
    .commute 24, .braid 25, .commute 27, .braid 28, .commute 30, .commute 31, .braid 32,
    .commute 34, .square 35, .commute 30, .braid 17, .commute 19, .commute 20, .commute 21,
    .commute 22, .commute 23, .commute 13, .commute 14, .commute 15, .commute 16, .braid 17,
    .commute 19, .commute 15, .commute 12, .commute 13, .commute 5, .braid 3, .braid 5, .commute
    7, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .braid 13, .braid 15,
    .commute 17, .commute 18, .braid 19, .commute 21, .commute 22])
,
  ([6, 5, 2, 0, 1, 8, 0, 5, 6, 2, 1, 3, 2, 0, 8, 1, 0, 5, 6, 0, 1, 2, 3, 0, 8, 0, 1, 2, 5, 0, 8,
    1, 0, 5, 6, 1, 2], [6, 5, 0, 8, 1, 2, 0, 1, 3, 2, 5, 0, 8, 1, 0, 6, 5, 0, 6, 8, 1, 0, 5, 2,
    1, 0, 8, 3, 2, 1, 0, 5, 6], [.braid 23, .commute 25, .commute 26, .commute 27, .braid 28,
    .braid 30, .commute 32, .commute 33, .square 34, .commute 26, .commute 27, .commute 28,
    .commute 25, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13,
    .commute 14, .commute 15, .braid 16, .commute 7, .commute 8, .commute 9, .commute 10,
    .commute 6, .commute 4, .commute 2, .commute 3, .braid 4, .braid 6, .commute 8, .commute 9,
    .braid 10, .commute 12, .commute 13, .braid 14, .commute 16, .braid 17, .commute 19,
    .commute 20, .commute 21, .commute 22, .braid 23, .braid 25, .commute 27, .braid 28,
    .commute 30, .commute 31, .commute 32, .square 33, .commute 21, .commute 22, .commute 23,
    .commute 24, .commute 25, .commute 26, .commute 20, .commute 21, .commute 22, .commute 19,
    .braid 15, .commute 17])
,
  ([6, 5, 0, 8, 1, 2, 0, 1, 3, 2, 5, 0, 8, 1, 0, 6, 5, 0, 6, 8, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0,
    5, 6], [6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6], [.commute 18, .commute 14, .braid 15, .commute 17, .commute 12, .commute 13,
    .commute 14, .braid 15, .commute 12, .commute 13, .commute 9, .commute 10, .commute 11,
    .commute 12, .commute 8, .commute 9, .commute 10, .commute 11, .commute 9, .commute 7,
    .commute 8, .commute 5, .commute 6, .commute 7])
,
  ([2, 1, 0, 8, 0, 1, 2, 1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 1], [1, 0, 5, 2, 1, 0, 8, 0, 1, 2,
    0, 1], [.braid 5, .commute 7, .commute 8, .square 9, .commute 4, .braid 5, .commute 7,
    .square 8, .commute 3, .commute 4, .commute 2, .braid 0, .braid 2, .braid 4, .commute 6,
    .braid 7, .square 9, .braid 5, .commute 7, .square 8, .commute 4, .braid 5, .commute 3,
    .commute 1, .commute 2])
,
  ([1, 0, 5, 2, 1, 0, 8, 0, 1, 2, 0, 1, 2, 1, 0, 8, 0, 1, 2], [1, 0, 5, 0, 1], [.commute 9,
    .braid 7, .braid 9, .square 11, .square 10, .commute 8, .square 9, .commute 6, .commute 7,
    .square 8, .braid 4, .commute 6, .square 7, .commute 3, .braid 4, .square 6, .square 5])
,
  ([0, 8, 0, 2, 1, 0, 8, 0, 1, 2], [2, 1, 0, 8, 2, 0], [.braid 0, .commute 2, .commute 3, .braid
    4, .square 6, .commute 1, .braid 2, .commute 4, .square 5, .commute 0, .commute 1, .braid 2,
    .commute 4])
,
  ([0, 2, 8, 0, 1, 2], [0, 8, 0, 1, 2, 1], [.commute 1, .commute 2, .braid 3])
,
  ([0, 8, 0, 1, 2, 1, 2, 1, 0, 8, 0, 1, 2], [1, 2, 1], [.braid 3, .square 5, .square 4, .commute
    2, .square 3, .commute 1, .square 2, .commute 0, .square 1, .braid 0])
,
  ([1, 2, 1], [1, 2, 1], [])
,
  ([1, 2, 1, 1, 0, 5, 0, 1], [1, 0, 5, 2, 0, 1], [.square 2, .commute 1, .commute 2])
,
  ([1, 0, 5, 2, 0, 1, 1, 2, 1], [1, 0, 5, 0, 1], [.square 5, .commute 3, .square 4])
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
