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
/-- Exact bounded chunks of literal E8 square, commutation and braid moves, block 11. -/
def y431E8RewriteData11 : Fin 64 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
![
  ([3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 5], [3, 2, 1, 0, 8, 0,
    5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 2, 0], [.commute 21, .square 22, .commute 20])
,
  ([3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 2, 0, 1], [3, 2, 1, 0, 8, 0, 5,
    6, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 2, 0, 1], [])
,
  ([3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 2, 0, 1, 1, 0, 8, 1], [8, 0, 5,
    3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 5, 0, 1, 2, 0, 1], [.square 22, .square 21, .braid 14,
    .commute 16, .commute 17, .commute 18, .commute 19, .square 20, .commute 10, .commute 11,
    .commute 12, .commute 13, .braid 14, .commute 16, .commute 12, .commute 9, .commute 10,
    .braid 3, .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .braid 10, .braid 12,
    .commute 14, .commute 15, .braid 16, .commute 18, .commute 6, .commute 7, .commute 8,
    .commute 9, .commute 10, .commute 11, .commute 12, .braid 13, .commute 5, .commute 6,
    .commute 7, .commute 2, .braid 3, .commute 5, .commute 6, .braid 7, .commute 9, .commute 10,
    .braid 11, .commute 13, .commute 6, .commute 7, .commute 8, .commute 5, .commute 6, .commute
    7, .commute 4, .commute 1, .commute 2, .commute 3, .commute 0, .commute 1, .commute 2])
,
  ([8, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 5, 0, 1, 2, 0, 1, 0, 1, 0], [8, 0, 5, 3, 2, 1,
    0, 8, 3, 2, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1], [.braid 19, .square 21, .square 20])
,
  ([8, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1, 1, 0, 8, 0, 1], [3, 2, 1, 0, 8,
    0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 2, 0, 1], [.square 19, .commute 18, .commute
    19, .braid 16, .commute 18, .commute 13, .braid 11, .braid 13, .commute 15, .commute 16,
    .commute 17, .commute 14, .commute 12, .commute 10, .commute 11, .braid 12, .braid 14,
    .commute 16, .commute 7, .commute 8, .commute 9, .commute 10, .commute 6, .commute 7,
    .commute 2, .commute 3, .commute 4, .commute 5, .commute 6, .braid 7, .commute 9, .braid 10,
    .commute 12, .commute 13, .braid 14, .commute 12, .commute 6, .commute 7, .commute 8,
    .commute 9, .commute 10, .commute 11, .commute 5, .commute 6, .commute 7, .commute 8,
    .commute 9, .commute 10, .commute 1, .commute 2, .braid 3, .commute 5, .commute 6, .commute
    7, .commute 6, .commute 5, .commute 0, .commute 1, .commute 2, .braid 3])
,
  ([3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 2, 0, 1, 1, 0, 8, 0, 1], [8, 0,
    5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1], [.square 22, .square 21, .braid 14,
    .commute 16, .commute 17, .commute 18, .commute 19, .square 20, .commute 10, .commute 11,
    .commute 12, .commute 13, .braid 14, .commute 16, .commute 12, .commute 9, .commute 10,
    .braid 3, .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .braid 10, .braid 12,
    .commute 14, .commute 15, .braid 16, .commute 18, .square 19, .commute 6, .commute 7,
    .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .braid 13, .commute 5,
    .commute 6, .commute 7, .commute 2, .braid 3, .commute 5, .commute 6, .braid 7, .commute 9,
    .commute 10, .braid 11, .commute 13, .commute 6, .commute 7, .commute 8, .commute 5,
    .commute 6, .commute 7, .commute 4, .commute 1, .commute 2, .commute 3, .commute 0, .commute
    1, .commute 2])
,
  ([8, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 5, 0, 1, 2, 1, 6], [8, 0, 5, 3, 2, 1, 0, 8, 5,
    6, 3, 2, 1, 0, 5, 0, 1, 2, 1], [.commute 13, .braid 11, .braid 13, .commute 15, .commute 16,
    .commute 17, .commute 18, .square 19, .commute 12, .commute 10, .commute 11, .commute 9,
    .commute 10, .commute 8, .commute 9])
,
  ([8, 0, 5, 3, 2, 1, 0, 8, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 1, 5], [8, 0, 5, 3, 2, 1, 0, 8, 5, 6,
    5, 3, 0, 1, 2, 0, 1, 0], [.braid 13, .commute 15, .commute 16, .commute 17, .square 18,
    .commute 12, .braid 13, .commute 15, .commute 11, .commute 12, .braid 13, .braid 15,
    .commute 10])
,
  ([8, 0, 5, 3, 2, 1, 0, 8, 5, 6, 5, 3, 0, 1, 2, 0, 1, 0, 1, 2, 1], [8, 0, 5, 3, 2, 1, 0, 8, 5,
    6, 5, 3, 2, 1, 0], [.braid 15, .square 17, .braid 13, .commute 15, .square 16, .commute 12,
    .braid 13, .square 15])
,
  ([8, 0, 5, 3, 2, 1, 0, 8, 5, 6, 5, 3, 2, 1, 0, 8], [8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 5,
    6, 0], [.commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .braid
    13, .braid 7, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .commute 8,
    .commute 9, .commute 10, .commute 6, .commute 7, .commute 8, .commute 5, .commute 6,
    .commute 4, .commute 3, .braid 4, .braid 6, .braid 8, .braid 10, .commute 12, .commute 9,
    .commute 7, .commute 8, .commute 5, .commute 6, .commute 7])
,
  ([8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 5, 6, 0, 1, 0, 8, 0, 1], [8, 6, 0, 5, 3, 2, 1, 0, 8,
    5, 6, 5, 3, 2, 0], [.commute 12, .commute 13, .commute 7, .commute 8, .commute 9, .braid 10,
    .commute 12, .braid 13, .commute 15, .commute 6, .commute 7, .braid 8, .commute 10, .commute
    11, .commute 12, .braid 13, .braid 15, .square 17, .square 16, .commute 14, .square 15,
    .braid 12, .commute 5, .braid 6, .commute 8, .commute 9, .commute 10, .commute 11, .commute
    12, .braid 4, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .commute 11,
    .commute 3, .commute 4, .commute 5, .commute 6, .braid 7, .commute 2, .commute 3, .commute
    4, .braid 5, .commute 7, .braid 8, .commute 10, .braid 6, .commute 8, .commute 9, .commute
    5, .braid 6, .commute 8, .commute 4, .commute 5, .commute 3, .commute 4, .commute 2,
    .commute 3, .commute 1])
,
  ([8, 6, 0, 5, 3, 2, 1, 0, 8, 5, 6, 5, 3, 2, 0, 1, 0, 8, 0, 1], [8, 0, 5, 6, 2, 1, 0, 5, 3, 2,
    1, 0, 8, 5, 6, 0], [.commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute
    3, .commute 4, .commute 5, .braid 6, .commute 8, .commute 1, .commute 2, .commute 3,
    .commute 4, .commute 5, .braid 6, .braid 8, .commute 10, .commute 11, .braid 12, .commute
    14, .braid 15, .square 17, .braid 13, .commute 15, .square 16, .commute 12, .braid 13,
    .commute 7, .braid 5, .braid 7, .commute 9, .commute 10, .commute 11, .commute 12, .commute
    13, .commute 8, .commute 9, .commute 10, .commute 6, .commute 7, .commute 8, .commute 4,
    .commute 5, .commute 6, .commute 3, .commute 4, .commute 2, .commute 3, .braid 4, .braid 6,
    .braid 8, .braid 10, .commute 12, .commute 9, .commute 7, .commute 8, .commute 5, .commute
    6, .commute 7])
,
  ([8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 5, 6, 0, 8, 1, 0], [8, 0, 5, 3, 2, 1, 0, 8, 5, 6, 5,
    3, 2, 0, 1], [.commute 12, .commute 13, .commute 7, .commute 8, .commute 9, .braid 10,
    .commute 12, .braid 13, .square 15, .commute 6, .commute 7, .braid 8, .commute 10, .commute
    11, .commute 12, .braid 13, .square 15, .commute 5, .braid 6, .commute 8, .commute 9,
    .commute 10, .commute 11, .braid 4, .commute 6, .commute 7, .commute 8, .commute 9, .commute
    10, .commute 3, .commute 4, .commute 5, .commute 6, .braid 7, .commute 9, .commute 8,
    .commute 7])
,
  ([8, 0, 5, 3, 2, 1, 0, 8, 5, 6, 5, 3, 2, 0, 1, 1], [8, 0, 5, 3, 2, 1, 0, 8, 5, 6, 5, 3, 2, 0],
    [.square 14])
,
  ([8, 0, 5, 3, 2, 1, 0, 8, 5, 6, 5, 3, 2, 0, 8], [8, 6, 0, 5, 3, 2, 1, 0, 8, 5, 6, 5, 3, 2, 0],
    [.commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .braid 12, .commute 11,
    .commute 12, .commute 10, .commute 11, .commute 2, .commute 3, .commute 4, .braid 5,
    .commute 7, .braid 8, .commute 10, .braid 6, .commute 8, .commute 9, .commute 5, .braid 6,
    .commute 8, .commute 4, .commute 5, .commute 3, .commute 4, .commute 2, .commute 3, .commute
    1])
,
  ([8, 6, 0, 5, 3, 2, 1, 0, 8, 5, 6, 5, 3, 2, 0, 0], [8, 6, 0, 5, 3, 2, 1, 0, 8, 5, 6, 5, 3, 2],
    [.square 14])
,
  ([8, 6, 0, 5, 3, 2, 1, 0, 8, 5, 6, 5, 3, 2, 2], [8, 6, 0, 5, 3, 2, 1, 0, 8, 5, 6, 5, 3],
    [.square 13])
,
  ([8, 6, 0, 5, 3, 2, 1, 0, 8, 5, 6, 5, 3, 6], [8, 6, 0, 5, 3, 2, 1, 0, 8, 6, 5, 3], [.braid 9,
    .commute 11, .square 12])
,
  ([8, 6, 0, 5, 3, 2, 1, 0, 8, 6, 5, 3, 8], [8, 0, 5, 6, 3, 2, 1, 0, 5, 3, 0], [.commute 8,
    .commute 9, .commute 10, .square 11, .commute 7, .commute 3, .commute 4, .commute 5,
    .commute 1, .commute 2, .commute 3, .commute 4, .braid 5, .braid 7, .commute 9, .commute 4,
    .commute 5, .commute 3, .commute 4, .commute 2, .commute 3])
,
  ([8, 0, 5, 6, 3, 2, 1, 0, 5, 3, 0, 1], [8, 0, 5, 6, 3, 2, 1, 0, 5, 3, 0, 1], [])
,
  ([8, 0, 5, 6, 3, 2, 1, 0, 5, 3, 0, 1, 1], [8, 0, 5, 6, 3, 2, 1, 0, 5, 3, 0], [.square 11])
,
  ([8, 0, 5, 6, 3, 2, 1, 0, 5, 3, 0, 1, 5], [8, 0, 5, 6, 5, 2, 3, 2, 0, 1, 0], [.commute 8,
    .commute 7, .braid 8, .commute 10, .square 11, .commute 6, .commute 7, .braid 8, .braid 4,
    .commute 6, .commute 5, .commute 4])
,
  ([8, 0, 5, 6, 5, 2, 3, 2, 0, 1, 0, 0], [8, 0, 5, 6, 5, 2, 3, 2, 0, 1], [.square 10])
,
  ([8, 0, 5, 6, 5, 2, 3, 2, 0, 1, 6], [8, 6, 0, 5, 2, 3, 2, 0, 1], [.braid 2, .commute 4,
    .commute 5, .commute 6, .commute 7, .commute 8, .square 9, .commute 1])
,
  ([8, 6, 0, 5, 2, 3, 2, 0, 1, 1], [8, 6, 0, 5, 2, 3, 2, 0], [.square 8])
,
  ([8, 6, 0, 5, 2, 3, 2, 0, 8], [6, 5, 0, 8, 0, 5, 2, 3, 2], [.commute 6, .commute 7, .commute
    5, .commute 6, .commute 4, .commute 5, .braid 2, .commute 4, .commute 0, .commute 1, .braid
    2])
,
  ([6, 5, 0, 8, 0, 5, 2, 3, 2, 5], [6, 5, 0, 8, 2, 3, 2, 0], [.commute 5, .commute 6, .commute
    7, .square 8, .commute 4, .commute 5, .commute 6])
,
  ([6, 5, 0, 8, 2, 3, 2, 0, 0], [6, 5, 0, 8, 2, 3, 2], [.square 7])
,
  ([6, 5, 0, 8, 2, 3, 2, 1], [6, 5, 0, 8, 2, 3, 2, 1], [])
,
  ([6, 5, 0, 8, 2, 3, 2, 1, 2], [6, 5, 0, 8, 2, 3, 1, 2, 1], [.braid 6])
,
  ([6, 5, 0, 8, 2, 3, 1, 2, 1, 6], [6, 5, 0, 8, 6, 2, 3, 1, 2, 1], [.commute 8, .commute 7,
    .commute 6, .commute 5, .commute 4])
,
  ([6, 5, 0, 8, 6, 2, 3, 1, 2, 1, 8], [5, 6, 5, 2, 3, 0, 1, 2, 1], [.commute 3, .commute 4,
    .commute 5, .commute 6, .commute 7, .commute 8, .square 9, .commute 2, .commute 3, .commute
    4, .braid 0])
,
  ([5, 6, 5, 2, 3, 0, 1, 2, 1, 5], [5, 6, 0, 5, 2, 3, 0, 1, 2, 1], [.commute 8, .commute 7,
    .commute 6, .commute 2, .commute 3, .braid 4, .commute 3, .commute 4, .commute 2, .commute
    3])
,
  ([5, 6, 0, 5, 2, 3, 0, 1, 2, 1, 1], [5, 6, 0, 5, 2, 3, 0, 1, 2], [.square 9])
,
  ([5, 6, 0, 5, 2, 3, 0, 1, 2, 0, 3], [5, 6, 0, 5, 0, 1, 2, 3, 1, 2, 0], [.commute 9, .commute
    5, .commute 6, .braid 7, .commute 4, .braid 5, .commute 7])
,
  ([5, 6, 0, 5, 0, 1, 2, 3, 1, 2, 0, 0], [5, 6, 0, 5, 0, 1, 2, 3, 1, 2], [.square 10])
,
  ([5, 6, 0, 5, 0, 1, 2, 3, 1, 2, 3], [5, 6, 0, 5, 2, 3, 0, 1, 2], [.commute 7, .braid 5, .braid
    7, .square 9, .commute 6, .commute 4, .commute 5])
,
  ([5, 6, 0, 5, 2, 3, 0, 1, 2, 1], [5, 6, 0, 5, 2, 3, 0, 1, 2, 1], [])
,
  ([5, 6, 0, 5, 2, 3, 0, 1, 2, 1, 5], [5, 6, 5, 2, 3, 0, 1, 2, 1], [.commute 3, .commute 4,
    .commute 2, .commute 3, .braid 4, .commute 6, .commute 7, .commute 8, .square 9, .commute 3,
    .commute 2])
,
  ([1, 2, 1, 0, 3, 2, 5, 6, 5], [2, 1, 0, 5, 6, 5, 2, 3, 2], [.commute 5, .commute 6, .commute
    7, .commute 4, .commute 5, .commute 6, .braid 0, .commute 2, .commute 3, .commute 4,
    .commute 5])
,
  ([5, 6, 5, 2, 3, 0, 1, 2, 1, 6], [6, 5, 2, 3, 0, 1, 2, 1], [.braid 0, .commute 2, .commute 3,
    .commute 4, .commute 5, .commute 6, .commute 7, .square 8])
,
  ([1, 2, 1, 0, 3, 2, 5, 6], [2, 1, 0, 5, 6, 2, 3, 2], [.commute 5, .commute 6, .commute 4,
    .commute 5, .braid 0, .commute 2, .commute 3, .commute 4])
,
  ([5, 6, 5, 2, 3, 0, 1, 2, 1, 2, 1, 0, 5, 6, 2, 3, 2], [5], [.braid 6, .square 8, .square 7,
    .commute 5, .square 6, .commute 2, .commute 3, .commute 4, .square 5, .commute 1, .commute
    2, .commute 3, .square 4, .square 3, .square 2, .square 1])
,
  ([6, 5, 2, 3, 0, 1, 2, 1, 2], [6, 5, 2, 3, 2, 0, 1], [.braid 5, .square 7, .commute 4])
,
  ([2, 1, 0, 5, 6, 5, 2, 3, 2, 5], [2, 1, 0, 5, 6, 2, 3, 2], [.commute 5, .commute 6, .commute
    7, .square 8])
,
  ([6, 5, 2, 3, 2, 0, 1, 2, 1, 0, 5, 6, 2, 3, 2], [2, 1, 0, 5, 6, 5, 0, 1, 2], [.commute 4,
    .braid 5, .square 7, .commute 6, .commute 7, .commute 8, .square 9, .commute 3, .commute 4,
    .commute 5, .commute 6, .commute 7, .square 8, .braid 3, .commute 5, .commute 6, .commute 1,
    .commute 2, .braid 3, .commute 5, .commute 0, .commute 1, .commute 2, .braid 3])
,
  ([5, 2, 1, 0, 5, 6, 5, 0, 1, 2], [2, 1, 0, 5, 6, 0, 5, 0, 1, 2], [.commute 0, .commute 1,
    .braid 2, .commute 4])
,
  ([2, 1, 0, 5, 6, 5, 0, 1, 2, 2, 1, 0, 5, 6, 0, 5, 0, 1, 2], [5], [.square 8, .square 7,
    .square 6, .square 5, .square 4, .braid 2, .square 4, .square 3, .commute 1, .square 2,
    .commute 0, .square 1])
,
  ([2, 1, 0, 5, 6, 5, 0, 1, 2, 6, 5, 2, 3, 0, 1, 2, 1], [6, 5, 2, 3, 2, 0, 1], [.braid 3,
    .commute 5, .commute 6, .commute 7, .square 8, .commute 2, .braid 3, .commute 5, .commute 6,
    .square 7, .square 6, .commute 1, .commute 2, .braid 3, .commute 5, .square 6, .commute 4,
    .square 5, .commute 3, .commute 4, .commute 0, .commute 1])
,
  ([6, 5, 2, 3, 2, 0, 1, 3], [6, 5, 3, 2, 0, 1], [.braid 2, .commute 4, .commute 5, .square 6])
,
  ([2, 1, 0, 5, 6, 5, 2, 3, 2, 2, 1, 0, 5, 6, 0, 5, 0, 1, 2], [1, 0, 5, 6, 2, 3, 2], [.square 8,
    .braid 3, .commute 5, .commute 6, .commute 7, .commute 8, .commute 4, .commute 5, .commute
    6, .commute 2, .commute 3, .commute 4, .commute 1, .commute 0, .braid 1, .commute 3, .braid
    4, .braid 6, .braid 8, .square 10, .commute 7, .commute 0, .commute 1, .commute 2, .commute
    3, .commute 4, .braid 5, .braid 7, .square 9, .square 8, .square 7, .commute 4, .commute 5,
    .square 6, .commute 2, .commute 3, .commute 4, .commute 1, .commute 2, .commute 3])
,
  ([6, 5, 3, 2, 0, 1, 1, 0, 5, 6, 2, 3, 2], [2], [.square 5, .square 4, .commute 1, .commute 2,
    .square 3, .commute 0, .commute 1, .square 2, .square 1, .square 0])
,
  ([6, 5, 2, 3, 2, 0, 1, 3, 1], [6, 5, 3, 2, 0], [.braid 2, .commute 4, .commute 5, .square 6,
    .square 5])
,
  ([0, 2, 3, 5, 6], [0, 5, 6, 2, 3], [.commute 2, .commute 3, .commute 1, .commute 2])
,
  ([6, 5, 2, 3, 2, 0, 1, 1], [6, 5, 2, 3, 2, 0], [.square 6])
,
  ([6, 5, 2, 3, 2, 0, 1, 0, 5, 6, 2, 3, 2], [3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3], [.braid 2,
    .commute 4, .commute 5, .commute 6, .commute 7, .commute 8, .braid 9, .square 11, .braid 4,
    .commute 6, .commute 7, .commute 1, .commute 2, .commute 3, .braid 4, .commute 6, .commute
    0, .commute 1, .commute 2, .commute 3, .braid 4])
,
  ([3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3], [3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3], [])
,
  ([5, 2, 2], [5], [.square 1])
,
  ([2, 3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3], [3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3, 2], [.braid 0,
    .commute 2, .commute 3, .commute 4, .commute 5, .commute 6, .commute 7, .commute 8, .braid
    9])
,
  ([2, 3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3, 2], [3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3], [.braid 0,
    .commute 2, .commute 3, .commute 4, .commute 5, .commute 6, .commute 7, .commute 8, .braid
    9, .square 11])
,
  ([3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3, 5], [3, 2, 1, 0, 5, 6, 0, 5, 0, 1, 2, 3], [.commute 10,
    .commute 9, .commute 8, .braid 6])
,
  ([3, 2, 1, 0, 5, 6, 0, 5, 0, 1, 2, 3, 3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3], [5], [.square 11,
    .square 10, .square 9, .square 8, .square 7, .commute 5, .square 6, .braid 3, .square 5,
    .square 4, .commute 2, .square 3, .commute 1, .square 2, .commute 0, .square 1])
,
  ([0, 5, 6, 2, 3, 3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3, 2], [1, 0, 5, 6, 2, 3, 2], [.square 4,
    .square 3, .commute 2, .commute 3, .braid 4, .square 6, .commute 1, .braid 2, .commute 4,
    .square 5, .braid 0, .commute 2, .commute 3, .square 4])
,
  ([2, 3, 2, 6, 5, 0, 1], [6, 5, 2, 3, 2, 0, 1], [.commute 2, .commute 3, .commute 1, .commute
    2, .commute 0, .commute 1])
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
