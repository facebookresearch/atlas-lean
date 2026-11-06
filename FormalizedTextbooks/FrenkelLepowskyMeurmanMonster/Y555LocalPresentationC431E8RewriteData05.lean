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
/-- Exact bounded chunks of literal E8 square, commutation and braid moves, block 5. -/
def y431E8RewriteData05 : Fin 64 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
![
  ([0, 1, 8, 0, 5, 6, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 1, 2, 0, 1, 8, 0, 8, 5, 2, 1, 0, 8, 1, 2,
    1], [1, 0, 8, 5, 6, 0, 1, 5, 0, 8, 2, 1, 6, 5, 0, 5, 1, 2, 8, 0, 6, 5, 1, 0, 8, 1, 0, 5, 0,
    1, 2, 1], [.commute 23, .commute 24, .commute 25, .braid 26, .commute 23, .commute 24,
    .commute 22, .commute 20, .commute 18, .commute 19, .braid 20, .braid 22, .braid 24,
    .commute 26, .commute 19, .commute 20, .braid 17, .commute 19, .braid 20, .commute 22,
    .commute 23, .braid 24, .commute 22, .commute 5, .commute 6, .commute 4, .braid 2, .braid 4,
    .braid 6, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .braid
    14, .commute 7, .commute 5, .braid 0, .commute 2, .commute 3, .commute 4, .braid 5, .braid
    7, .commute 9, .commute 10, .commute 11, .braid 12, .commute 14, .braid 15, .commute 17,
    .commute 18, .commute 19, .braid 20, .braid 22, .commute 24, .braid 13, .commute 15,
    .commute 16, .commute 17, .commute 18, .commute 19, .commute 12, .braid 13])
,
  ([1, 0, 8, 5, 6, 0, 1, 5, 0, 8, 2, 1, 6, 5, 0, 5, 1, 2, 8, 0, 6, 5, 1, 0, 8, 1, 0, 5, 0, 1, 2,
    1], [1, 8, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 1, 5, 0, 5, 6, 8, 0, 1, 5, 0, 8, 5, 6, 1, 0, 5, 0,
    1, 2, 1], [.commute 15, .commute 16, .commute 17, .commute 11, .commute 12, .braid 13,
    .commute 15, .commute 9, .commute 10, .commute 11, .commute 8, .commute 9, .commute 7,
    .commute 4, .commute 5, .commute 6, .braid 7, .braid 9, .braid 11, .commute 13, .commute 14,
    .braid 15, .braid 17, .braid 19, .commute 21, .commute 22, .commute 23, .commute 20,
    .commute 18, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .commute 11,
    .braid 12, .commute 5, .commute 6, .braid 3, .commute 5, .braid 6, .commute 8, .commute 9,
    .braid 10, .commute 12, .braid 13, .commute 15, .commute 16, .commute 17, .braid 18, .braid
    20, .commute 22, .commute 15, .commute 16, .commute 8, .braid 1, .commute 3, .commute 4,
    .commute 5, .braid 6, .braid 8, .commute 10, .commute 11, .commute 12])
,
  ([1, 8, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 1, 5, 0, 5, 6, 8, 0, 1, 5, 0, 8, 5, 6, 1, 0, 5, 0, 1, 2,
    1], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 1, 0, 5, 0,
    1, 2, 1], [.braid 13, .commute 15, .braid 16, .commute 18, .commute 19, .braid 20, .commute
    18, .commute 4, .commute 5, .commute 6, .commute 3, .commute 0, .braid 1, .braid 3, .commute
    5, .braid 6, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .braid 13,
    .commute 15, .braid 16, .braid 18, .commute 20, .braid 9, .commute 11, .commute 12, .commute
    13, .commute 14, .commute 15, .commute 16, .commute 8, .braid 9, .commute 11, .commute 12,
    .commute 13, .commute 12, .commute 11, .commute 5, .commute 6, .commute 7, .commute 8,
    .braid 9, .commute 4, .commute 2, .commute 3])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2,
    1, 0], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 1, 0, 5,
    0, 1, 2, 1, 0], [])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2,
    1, 0, 3], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 1, 0,
    5, 0, 1, 2, 3, 1, 0], [.commute 32, .commute 31])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2,
    3, 1, 0, 0], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 1,
    0, 5, 0, 1, 2, 3, 1], [.square 33])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2,
    3, 1, 8], [8, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 6, 5, 0, 1, 0, 8, 0, 5, 6, 5, 0, 8, 1, 0, 5, 8,
    0, 1, 2, 3, 1], [.commute 20, .braid 18, .braid 20, .commute 22, .commute 23, .commute 24,
    .commute 16, .commute 15, .braid 16, .commute 18, .commute 19, .braid 20, .commute 22,
    .commute 18, .braid 9, .commute 11, .commute 12, .commute 13, .commute 14, .commute 15,
    .braid 16, .braid 18, .commute 20, .commute 21, .braid 22, .braid 24, .commute 26, .commute
    12, .commute 13, .commute 11, .commute 12, .braid 13, .commute 15, .commute 16, .commute 17,
    .commute 18, .braid 19, .commute 8, .braid 9, .commute 11, .commute 12, .braid 13, .commute
    15, .commute 16, .braid 17, .commute 19, .braid 20, .commute 22, .commute 23, .braid 24,
    .braid 26, .commute 28, .commute 29, .commute 30, .commute 31, .square 32, .commute 22,
    .commute 15, .commute 7, .commute 8, .braid 9, .commute 11, .commute 12, .braid 13])
,
  ([8, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 6, 5, 0, 1, 0, 8, 0, 5, 6, 5, 0, 8, 1, 0, 5, 8, 0, 1, 2, 3,
    1], [8, 1, 0, 5, 8, 0, 1, 6, 2, 5, 0, 8, 1, 0, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 8, 0, 1, 2,
    3, 0, 1], [.braid 15, .commute 17, .commute 18, .commute 19, .braid 20, .braid 22, .commute
    24, .commute 25, .braid 26, .commute 28, .commute 29, .commute 10, .commute 11, .commute 12,
    .commute 9, .commute 10, .commute 8, .commute 6, .commute 3, .commute 4, .commute 5, .braid
    6, .braid 8, .braid 10, .braid 12, .commute 14, .commute 15, .commute 16, .commute 17,
    .commute 18, .commute 19, .commute 20, .commute 13, .commute 11, .commute 5, .commute 6,
    .commute 2, .braid 3, .commute 5, .braid 6, .commute 8, .commute 9, .commute 10, .braid 11,
    .braid 13, .commute 15, .commute 16, .commute 17, .commute 8, .commute 9, .braid 1, .commute
    3, .commute 4, .commute 5, .braid 6, .commute 8, .braid 9, .commute 11, .commute 12, .braid
    13, .commute 15, .commute 4, .commute 5, .commute 6])
,
  ([8, 1, 0, 5, 8, 0, 1, 6, 2, 5, 0, 8, 1, 0, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 8, 0, 1, 2, 3, 0,
    1], [1, 0, 8, 5, 0, 6, 1, 0, 5, 6, 0, 1, 2, 8, 0, 1, 5, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3,
    0, 1, 0], [.commute 7, .commute 3, .commute 0, .braid 1, .braid 3, .commute 5, .commute 6,
    .braid 7, .commute 9, .commute 10, .commute 11, .commute 12, .braid 13, .braid 15, .braid
    17, .commute 19, .braid 20, .commute 22, .commute 23, .commute 24, .commute 25, .braid 26,
    .commute 28, .braid 29, .commute 23, .commute 19, .commute 20, .braid 21, .commute 18,
    .braid 19, .commute 21, .braid 17, .commute 19, .commute 20, .commute 14, .braid 12, .braid
    14, .commute 16, .commute 17, .commute 18, .commute 19, .commute 15, .commute 16, .commute
    13, .commute 14, .commute 11, .commute 12, .commute 6, .commute 7, .commute 8, .commute 9,
    .commute 10, .commute 11, .braid 12, .braid 14, .braid 16, .commute 18, .commute 9, .commute
    10, .commute 11, .commute 12, .braid 7, .commute 9, .commute 5])
,
  ([1, 0, 8, 5, 0, 6, 1, 0, 5, 6, 0, 1, 2, 8, 0, 1, 5, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1,
    0], [6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3,
    0, 1, 0], [.commute 4, .braid 5, .commute 7, .commute 8, .braid 9, .commute 11, .braid 12,
    .commute 14, .commute 15, .braid 16, .commute 14, .commute 4, .commute 5, .braid 6, .commute
    3, .braid 4, .commute 6, .braid 7, .commute 9, .commute 10, .commute 11, .braid 12, .braid
    14, .commute 16, .commute 10, .commute 11, .commute 12, .commute 9, .commute 2, .braid 0,
    .braid 2, .commute 4, .commute 5, .commute 6, .braid 7, .braid 9, .commute 11, .braid 12,
    .commute 14, .commute 15, .braid 4, .commute 6, .commute 7, .commute 3, .braid 4, .commute
    6, .commute 2, .commute 3, .braid 4, .commute 1, .commute 2, .commute 0])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1,
    0, 1], [6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2,
    3, 1, 0], [.braid 29, .square 31])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 1, 0,
    5], [6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 1,
    0], [.braid 23, .commute 25, .commute 26, .commute 27, .commute 28, .commute 22, .braid 23,
    .commute 25, .commute 26, .commute 21, .commute 22, .braid 23, .commute 25, .braid 26,
    .braid 28, .square 30, .commute 27, .commute 25, .commute 26, .commute 24, .commute 25,
    .braid 22, .commute 24, .commute 21, .braid 22])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 1, 0,
    6], [6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 1, 0],
    [.commute 20, .commute 21, .commute 19, .braid 17, .braid 19, .braid 21, .commute 23,
    .commute 24, .commute 25, .commute 26, .commute 27, .commute 28, .square 29, .commute 20,
    .commute 18, .commute 19, .commute 16, .commute 17, .commute 18])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 1, 0, 0],
    [6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 1],
    [.square 28])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 1, 2], [6,
    0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 1, 2], [])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 1, 2, 5],
    [6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 0, 1, 2, 3, 0, 1, 2, 0],
    [.braid 21, .commute 23, .commute 24, .commute 25, .commute 26, .commute 27, .square 28,
    .commute 20, .braid 21, .commute 23, .commute 24, .commute 19, .commute 20, .braid 21,
    .commute 23, .braid 24, .commute 26])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 0, 1, 2, 3, 0, 1, 2, 0, 6], [6,
    0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 0, 1, 2, 3, 0, 1, 2, 0], [.braid 17,
    .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25,
    .commute 26, .square 27, .commute 16])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 0, 1, 2, 3, 0, 1, 2, 0, 1], [6, 0,
    5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 0, 1, 2, 3, 0, 1, 2, 0, 1], [])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 0, 1, 2, 3, 0, 1, 2, 0, 1, 0], [6,
    0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 0, 1, 2, 3, 0, 1, 2, 0, 1, 0], [])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 0, 1, 2, 3, 0, 1, 2, 0, 1, 0, 5],
    [6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1, 2, 1],
    [.braid 26, .commute 28, .braid 24, .commute 26, .commute 27, .commute 23, .braid 24,
    .commute 26, .braid 17, .commute 19, .commute 20, .commute 21, .commute 22, .commute 23,
    .braid 24, .braid 20, .commute 22, .commute 23, .commute 24, .commute 19, .braid 20,
    .commute 22, .commute 23, .commute 18, .commute 19, .braid 20, .commute 22, .commute 17,
    .commute 18, .commute 19, .braid 20])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1, 2, 1,
    2], [6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 2, 0, 1],
    [.braid 27, .square 29, .commute 26])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 2, 0, 1, 6],
    [6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3, 2, 0, 1],
    [.commute 28, .commute 27, .commute 26, .commute 25, .commute 24, .commute 23, .commute 22,
    .commute 16, .commute 17, .commute 18, .commute 19, .braid 20])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3, 2, 0, 1,
    8], [6, 0, 5, 1, 8, 0, 1, 2, 8, 3, 0, 5, 6, 0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 1, 2, 3,
    2, 1], [.commute 29, .commute 27, .commute 28, .commute 26, .commute 27, .commute 25,
    .commute 26, .braid 23, .commute 25, .braid 20, .commute 22, .commute 23, .commute 24,
    .commute 21, .commute 19, .commute 18, .braid 19, .braid 21, .commute 23, .commute 15,
    .commute 16, .commute 17, .commute 14, .commute 15, .commute 16, .braid 17, .commute 19,
    .commute 20, .braid 21, .commute 19, .commute 11, .commute 12, .commute 13, .commute 14,
    .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .braid 14,
    .commute 16, .braid 17, .braid 19, .commute 21, .commute 13, .commute 14, .commute 15,
    .commute 16, .commute 17, .commute 11, .commute 12, .commute 13, .commute 14, .commute 9,
    .commute 10, .commute 7, .commute 8, .commute 9, .braid 10, .commute 12, .braid 4, .commute
    6, .commute 7])
,
  ([6, 0, 5, 1, 8, 0, 1, 2, 8, 3, 0, 5, 6, 0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 1, 2, 3, 2,
    1], [6, 8, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 1, 2, 3,
    2, 1], [.commute 8, .commute 3, .braid 4, .commute 6, .commute 7, .braid 8, .commute 10,
    .commute 11, .braid 12, .braid 14, .commute 16, .braid 17, .commute 19, .commute 20,
    .commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13,
    .commute 14, .commute 15, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10,
    .commute 11, .commute 5, .braid 3, .braid 5, .commute 7, .commute 8, .braid 1, .commute 3,
    .commute 4, .braid 5, .commute 7, .braid 8, .commute 10, .braid 11, .commute 13, .commute
    14, .braid 15, .commute 17, .commute 18, .commute 19, .commute 7, .commute 8, .commute 9,
    .commute 6, .braid 4, .braid 6, .commute 8, .braid 2, .commute 4, .commute 5, .braid 6,
    .commute 4, .commute 1, .braid 2, .braid 4, .commute 6])
,
  ([6, 8, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 1, 2, 3, 2,
    1], [8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 1, 2, 3,
    2, 1], [.commute 0])
,
  ([8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 1, 2, 3, 2, 1,
    0], [8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 1, 2, 3,
    2, 1, 0], [])
,
  ([8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 1, 2, 3, 2, 1,
    0, 5], [8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 3, 2,
    1, 0, 5, 2, 3], [.braid 27, .commute 29, .commute 30, .commute 31, .commute 26, .braid 27,
    .commute 29, .commute 30])
,
  ([8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5,
    2, 3, 6], [8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2,
    1, 0, 5, 2, 3], [.commute 25, .commute 26, .commute 27, .commute 28, .commute 24, .commute
    25, .commute 26, .commute 23, .commute 24, .commute 22, .braid 20, .braid 22, .braid 24,
    .braid 26, .braid 28, .commute 30, .commute 31, .square 32, .commute 27, .commute 25,
    .commute 26, .commute 23, .commute 24, .commute 25, .commute 21, .commute 22, .commute 23,
    .commute 24])
,
  ([8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 2,
    3, 1], [8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1,
    0, 5, 2, 3, 1], [])
,
  ([8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 2,
    3, 1, 0], [8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2,
    1, 0, 5, 2, 3, 1, 0], [])
,
  ([8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 2,
    3, 1, 0, 2], [8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3,
    2, 1, 0, 5, 2, 3, 1, 2, 0], [.commute 33])
,
  ([8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 2,
    3, 1, 2, 0, 5], [8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6,
    1, 0, 5, 2, 3, 1, 2, 1, 0], [.commute 29, .commute 30, .commute 31, .commute 32, .commute
    28, .commute 29, .braid 26, .commute 28, .braid 29, .commute 31, .braid 32, .square 34,
    .commute 25, .braid 26, .commute 28, .braid 29, .commute 31, .commute 30, .commute 29,
    .commute 27, .commute 28, .commute 26, .commute 27])
,
  ([8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 2, 3, 1,
    2, 1, 0, 6], [8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0,
    5, 2, 3, 1, 2, 1, 0], [.commute 24, .commute 25, .commute 23, .braid 21, .braid 23, .braid
    25, .commute 27, .commute 28, .commute 29, .commute 30, .commute 31, .commute 32, .square
    33, .commute 24, .commute 22, .commute 23, .commute 20, .commute 21, .commute 22])
,
  ([8, 6, 0, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2, 3, 1, 2,
    1, 0, 8], [8, 6, 5, 0, 1, 8, 0, 5, 6, 2, 3, 1, 0, 8, 2, 1, 0, 5, 6, 1, 2, 0, 1, 8, 0, 3, 2,
    1, 5, 0, 8, 3, 2, 0], [.braid 18, .commute 20, .commute 21, .commute 22, .commute 23,
    .commute 14, .commute 15, .commute 16, .commute 17, .braid 18, .commute 20, .commute 21,
    .commute 16, .commute 13, .commute 14, .commute 6, .braid 4, .braid 6, .commute 8, .commute
    9, .commute 10, .commute 11, .commute 12, .commute 13, .braid 14, .braid 16, .commute 18,
    .commute 19, .commute 13, .commute 14, .commute 11, .braid 2, .commute 4, .commute 5, .braid
    6, .commute 8, .commute 9, .commute 10, .braid 11, .commute 13, .braid 14, .commute 16,
    .commute 17, .commute 18, .braid 19, .braid 21, .braid 23, .commute 25, .commute 26,
    .commute 27, .commute 28, .commute 29, .commute 30, .braid 31, .braid 28, .commute 30,
    .commute 31, .braid 26, .commute 28, .commute 29, .commute 30, .commute 25, .commute 26,
    .commute 27])
,
  ([8, 6, 5, 0, 1, 8, 0, 5, 6, 2, 3, 1, 0, 8, 2, 1, 0, 5, 6, 1, 2, 0, 1, 8, 0, 3, 2, 1, 5, 0, 8,
    3, 2, 0], [6, 5, 0, 8, 1, 0, 8, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2,
    1, 0, 8, 5, 3, 2, 0], [.commute 24, .commute 25, .commute 22, .commute 23, .commute 20,
    .commute 21, .commute 10, .commute 11, .commute 12, .commute 4, .commute 0, .commute 1,
    .braid 2, .braid 4, .commute 6, .commute 7, .braid 8, .commute 10, .commute 11, .braid 12,
    .commute 14, .commute 15, .commute 16, .commute 17, .commute 18, .commute 19, .commute 20,
    .braid 21, .braid 23, .braid 25, .braid 27, .commute 29, .commute 26, .commute 24, .commute
    25, .commute 22, .commute 23, .commute 24, .commute 17, .commute 18, .commute 19, .commute
    16, .braid 14, .braid 16, .commute 18, .commute 11, .commute 12, .commute 10, .commute 11,
    .braid 12, .commute 14, .commute 15, .braid 16, .commute 14, .commute 11, .commute 12,
    .commute 13, .commute 10, .commute 11, .commute 12, .commute 9, .commute 8, .commute 7,
    .commute 6])
,
  ([6, 5, 0, 8, 1, 0, 8, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 5,
    3, 2, 0], [6, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2,
    1, 0, 8, 5, 3, 2, 0], [.commute 3, .braid 4, .braid 2, .commute 4])
,
  ([6, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 5,
    3, 2, 0, 1], [6, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 5, 3, 2, 0, 1], [])
,
  ([6, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 5,
    3, 2, 0, 1, 0], [6, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5,
    3, 2, 1, 0, 8, 5, 3, 2, 0, 1, 0], [])
,
  ([6, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 5,
    3, 2, 0, 1, 0, 5], [6, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0,
    5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 0, 1], [.braid 33, .commute 35, .commute 30, .commute 31,
    .commute 32, .braid 33])
,
  ([6, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 0, 1, 8, 1], [6, 5, 0, 1, 8, 0, 5, 6, 2, 1, 3, 2, 0, 8, 1, 0, 5, 6, 0, 1, 2, 3,
    8, 0, 1, 2, 8, 5, 0, 8, 1, 0, 5, 8, 0], [.commute 29, .commute 30, .commute 31, .commute 28,
    .commute 29, .commute 27, .braid 25, .braid 27, .braid 29, .braid 31, .commute 33, .commute
    24, .commute 25, .commute 26, .commute 27, .commute 23, .commute 24, .braid 21, .commute 23,
    .braid 24, .commute 26, .braid 27, .commute 29, .commute 30, .braid 31, .braid 33, .commute
    35, .square 36, .square 35, .commute 29, .braid 16, .commute 18, .commute 19, .commute 20,
    .commute 21, .commute 22, .commute 12, .commute 13, .commute 14, .commute 15, .braid 16,
    .commute 18, .commute 14, .commute 11, .commute 12, .commute 4, .braid 2, .braid 4, .commute
    6, .commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .braid 12, .braid 14,
    .commute 16, .commute 17, .braid 18, .commute 20, .commute 21, .braid 22, .commute 24,
    .commute 25])
,
  ([6, 5, 0, 1, 8, 0, 5, 6, 2, 1, 3, 2, 0, 8, 1, 0, 5, 6, 0, 1, 2, 3, 8, 0, 1, 2, 8, 5, 0, 8, 1,
    0, 5, 8, 0], [6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1,
    0, 8, 3, 2, 1, 0, 5, 1, 0], [.commute 26, .braid 27, .braid 29, .commute 31, .commute 32,
    .commute 31, .commute 28, .braid 29, .braid 27, .commute 29, .commute 25, .commute 24,
    .braid 25, .commute 27, .commute 28, .commute 21, .commute 22, .commute 23, .commute 20,
    .commute 21, .commute 22, .braid 23, .commute 25, .commute 26, .commute 27, .commute 19,
    .commute 17, .commute 18, .braid 15, .commute 17, .commute 13, .commute 14, .braid 15,
    .commute 13, .commute 11, .commute 12, .commute 10, .commute 11, .commute 3])
,
  ([6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1,
    0, 5, 1, 0, 1], [6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2,
    1, 0, 8, 3, 2, 1, 0, 5, 0, 1, 0], [.braid 33])
,
  ([6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1,
    0, 5, 0, 1, 0, 6], [6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3,
    2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 1, 0], [.commute 35, .commute 34, .commute 33])
,
  ([6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1,
    0, 5, 6, 0, 1, 0, 8], [6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 3, 2, 5, 1, 8, 0, 5, 6, 1, 0, 8, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 0, 1], [.braid 34, .commute 36, .commute 27, .commute
    28, .commute 29, .commute 26, .commute 27, .commute 25, .braid 23, .braid 25, .braid 27,
    .braid 29, .commute 31, .commute 32, .commute 33, .braid 34, .commute 32, .commute 33,
    .commute 34, .commute 31, .commute 28, .braid 29, .braid 31, .commute 33, .braid 27,
    .commute 29, .commute 30, .braid 31, .commute 29, .commute 22, .commute 23, .commute 24,
    .commute 25, .commute 26, .braid 27, .braid 29, .commute 31, .commute 25, .commute 26,
    .commute 27, .commute 24, .commute 21, .commute 22, .braid 15, .commute 17, .commute 18,
    .commute 19, .commute 20, .commute 21, .braid 22, .braid 24, .commute 26, .braid 27,
    .commute 29, .commute 30, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25,
    .commute 20, .commute 21, .commute 11, .commute 12])
,
  ([6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 3, 2, 5, 1, 8, 0, 5, 6, 1, 0, 8, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    2, 1, 0, 5, 6, 0, 1], [6, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1,
    0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 1], [.commute 13, .commute 14, .braid 15, .commute
    17, .braid 18, .commute 20, .braid 21, .commute 23, .commute 24, .braid 25, .commute 27,
    .commute 28, .commute 29, .commute 17, .commute 18, .commute 19, .commute 16, .commute 13,
    .braid 14, .braid 16, .commute 18, .commute 10, .commute 11, .braid 12, .commute 14,
    .commute 15, .braid 16, .commute 14, .commute 11, .commute 12, .commute 13, .commute 10,
    .commute 11, .commute 12, .commute 9, .commute 8, .commute 7, .commute 6, .commute 3, .braid
    4, .braid 2, .commute 4])
,
  ([6, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6, 0, 1, 8], [6, 5, 0, 1, 8, 0, 5, 6, 2, 1, 3, 2, 0, 8, 1, 0, 5, 6, 0, 1, 2, 3,
    8, 0, 1, 8, 2, 5, 0, 8, 1, 0, 5, 6, 8, 0, 1], [.commute 29, .commute 30, .commute 31,
    .commute 28, .commute 29, .commute 27, .braid 25, .braid 27, .braid 29, .braid 31, .commute
    33, .commute 34, .commute 24, .commute 25, .commute 26, .commute 27, .commute 23, .commute
    24, .braid 21, .commute 23, .braid 24, .commute 26, .braid 27, .commute 29, .commute 30,
    .braid 31, .commute 33, .braid 34, .commute 36, .square 37, .commute 29, .braid 16, .commute
    18, .commute 19, .commute 20, .commute 21, .commute 22, .commute 12, .commute 13, .commute
    14, .commute 15, .braid 16, .commute 18, .commute 14, .commute 11, .commute 12, .commute 4,
    .braid 2, .braid 4, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .commute
    11, .braid 12, .braid 14, .commute 16, .commute 17, .braid 18, .commute 20, .commute 21,
    .braid 22, .commute 24])
,
  ([6, 5, 0, 1, 8, 0, 5, 6, 2, 1, 3, 2, 0, 8, 1, 0, 5, 6, 0, 1, 2, 3, 8, 0, 1, 8, 2, 5, 0, 8, 1,
    0, 5, 6, 8, 0, 1], [6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3,
    2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 1, 0], [.commute 25, .commute 26, .braid 27, .braid 29,
    .commute 31, .commute 32, .commute 33, .braid 34, .commute 32, .commute 31, .commute 28,
    .braid 29, .braid 27, .commute 29, .commute 25, .commute 24, .braid 25, .commute 27,
    .commute 28, .commute 21, .commute 22, .commute 23, .commute 20, .commute 21, .commute 22,
    .braid 23, .commute 25, .commute 26, .commute 27, .commute 19, .commute 17, .commute 18,
    .braid 15, .commute 17, .commute 13, .commute 14, .braid 15, .commute 13, .commute 11,
    .commute 12, .commute 10, .commute 11, .commute 3])
,
  ([6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1,
    0, 5, 6, 0, 1, 0, 0, 1, 0], [6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1,
    0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [.square 36, .square 35, .square 34])
,
  ([6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1,
    0, 5, 6, 8], [6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0,
    8, 3, 2, 1, 0, 5, 6], [.commute 27, .commute 28, .commute 29, .commute 26, .commute 27,
    .commute 25, .braid 23, .braid 25, .braid 27, .braid 29, .commute 31, .commute 32, .square
    33, .commute 28, .commute 26, .commute 27, .commute 24, .commute 25, .commute 26])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 2, 0, 1, 0, 3], [6, 0, 5, 1, 0,
    8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 2, 3, 0, 1, 0], [.commute 23, .commute 22,
    .commute 21])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 2, 3, 0, 1, 0, 1], [6, 0, 5, 1,
    0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 2, 3, 1, 0], [.braid 22, .square 24])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 2, 3, 1, 0, 0], [6, 0, 5, 1, 0,
    8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 2, 3, 1], [.square 23])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 2, 3, 1, 5], [6, 0, 5, 1, 0, 8,
    0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 1, 2, 3, 1], [.commute 18, .commute 19, .commute 20,
    .commute 21, .square 22])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 1, 2, 3, 1, 2], [6, 0, 5, 1, 0, 8, 0,
    5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 1, 2, 3, 1, 2], [])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 1, 2, 3, 1, 2, 6], [6, 0, 5, 1, 0, 8,
    0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 1, 2, 3, 1, 2], [.commute 16, .commute 17, .commute 18,
    .commute 19, .commute 20, .commute 21, .square 22])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 1, 2, 3, 1, 2, 8], [8, 6, 0, 5, 1, 0, 8,
    0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 0, 1, 2, 0], [.braid 14, .commute 16, .commute 17, .commute
    18, .commute 19, .commute 20, .square 21, .commute 13, .braid 14, .commute 16, .commute 17,
    .commute 12, .commute 13, .braid 14, .commute 16, .braid 17, .commute 19, .commute 11,
    .braid 4, .commute 6, .commute 7, .commute 8, .braid 9, .commute 2, .commute 3, .braid 4,
    .commute 6, .braid 7, .commute 9, .commute 6, .commute 7, .commute 8, .commute 5, .commute
    2, .braid 3, .braid 5, .commute 7, .braid 1, .commute 3, .commute 4, .braid 5, .commute 3,
    .commute 0])
,
  ([8, 6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 0, 1, 2, 0, 0], [8, 6, 0, 5, 1, 0, 8, 0,
    5, 6, 1, 0, 5, 0, 1, 2, 3, 0, 1, 2], [.square 20])
,
  ([8, 6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 0, 1, 2, 5], [8, 6, 0, 5, 1, 0, 8, 0, 5,
    6, 0, 5, 0, 1, 2, 3, 0, 1, 2], [.braid 11, .commute 13, .commute 14, .commute 15, .commute
    10, .braid 11, .commute 13, .commute 14, .braid 15, .commute 17, .commute 18, .square 19,
    .commute 14, .commute 13, .commute 12, .braid 10])
,
  ([8, 6, 0, 5, 1, 0, 8, 0, 5, 6, 0, 5, 0, 1, 2, 3, 0, 1, 2, 6], [8, 6, 0, 5, 1, 0, 8, 5, 6, 0,
    5, 0, 1, 2, 3, 0, 1, 2], [.commute 9, .braid 7, .braid 9, .commute 11, .commute 12, .commute
    13, .commute 14, .commute 15, .commute 16, .commute 17, .square 18, .commute 8])
,
  ([8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 5, 0, 1, 2, 3, 0, 1, 2, 1], [8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 5,
    0, 1, 2, 3, 0, 1, 2, 1], [])
,
  ([8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 5, 0, 1, 2, 3, 0, 1, 2, 1, 0], [8, 6, 0, 5, 1, 0, 8, 5, 6, 0,
    5, 0, 1, 2, 3, 0, 1, 2, 1, 0], [])
,
  ([8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 5, 0, 1, 2, 3, 0, 1, 2, 1, 0, 2], [8, 6, 0, 5, 1, 0, 8, 5, 6,
    0, 5, 0, 1, 2, 3, 2, 0, 1, 0], [.braid 16, .commute 18, .square 19, .commute 15])
,
  ([8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 5, 0, 1, 2, 3, 2, 0, 1, 0, 5], [8, 6, 0, 5, 1, 0, 8, 5, 6, 3,
    2, 1, 0, 5, 0, 1, 2, 3, 0, 1], [.braid 16, .commute 18, .braid 9, .commute 11, .commute 12,
    .commute 13, .commute 14, .commute 15, .braid 16, .braid 12, .commute 14, .commute 15,
    .commute 16, .commute 11, .braid 12, .commute 14, .commute 15, .commute 10, .commute 11,
    .braid 12, .commute 14, .commute 9, .commute 10, .commute 11, .braid 12])
,
  ([8, 6, 0, 5, 1, 0, 8, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1, 6], [8, 6, 0, 5, 1, 0, 8, 3, 2,
    1, 0, 5, 6, 0, 5, 0, 1, 2, 3, 0, 1], [.commute 19, .commute 18, .commute 17, .commute 16,
    .commute 15, .commute 14, .commute 8, .commute 9, .commute 10, .commute 11, .braid 12,
    .commute 7, .commute 8, .commute 9, .braid 10, .commute 12])
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
