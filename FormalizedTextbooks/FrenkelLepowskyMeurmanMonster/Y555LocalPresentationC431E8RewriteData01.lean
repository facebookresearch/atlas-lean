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
def y431E8RewriteData01 : Fin 64 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
![
  ([6, 5, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 2, 3, 0, 1, 1], [6, 5, 0, 8, 5, 6, 1, 0, 5,
    2, 1, 0, 8, 5, 6, 1, 2, 3, 0], [.square 19])
,
  ([6, 5, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 2, 3, 0, 8], [5, 6, 0, 5, 2, 1, 0, 8, 1, 0,
    5, 6, 5, 1, 2, 3, 1, 0], [.commute 12, .commute 13, .commute 14, .commute 15, .commute 16,
    .commute 8, .commute 9, .braid 10, .commute 12, .commute 7, .braid 8, .commute 10, .commute
    11, .braid 12, .commute 14, .commute 15, .braid 16, .square 18, .braid 6, .commute 8,
    .commute 9, .commute 10, .commute 11, .braid 12, .commute 14, .commute 15, .commute 14,
    .commute 13, .commute 12, .commute 5, .commute 6, .commute 7, .braid 8, .commute 4, .commute
    5, .braid 6, .commute 8, .braid 9, .commute 11, .braid 7, .commute 9, .commute 10, .commute
    6, .braid 7, .commute 9, .commute 3, .commute 4, .commute 5, .commute 6, .braid 7, .commute
    4, .commute 5, .commute 2, .commute 3, .commute 1, .commute 0, .braid 1, .braid 3, .braid 5,
    .commute 7, .commute 0, .commute 1, .commute 2, .commute 3])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 5, 1, 2, 3, 1, 0, 6], [5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 0,
    5, 1, 2, 3, 1, 0], [.braid 10, .commute 12, .commute 13, .commute 14, .commute 15, .commute
    16, .square 17, .commute 9, .commute 8])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 1, 2, 3, 1, 0, 2], [5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5,
    1, 2, 3, 1, 2, 0], [.commute 16])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 1, 2, 3, 1, 2, 0, 0], [5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 0,
    5, 1, 2, 3, 1, 2], [.square 17])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 1, 2, 3, 1, 2, 5], [5, 6, 0, 5, 2, 1, 0, 8, 6, 0, 1, 2,
    3, 0, 1, 2], [.commute 11, .commute 12, .commute 13, .commute 14, .commute 15, .square 16,
    .braid 9, .commute 11, .commute 12])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 6, 0, 1, 2, 3, 0, 1, 2, 1], [5, 6, 0, 5, 2, 1, 0, 8, 6, 0, 1, 2, 3,
    0, 1, 2, 1], [])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 6, 0, 1, 2, 3, 0, 1, 2, 1, 8], [6, 5, 0, 8, 5, 6, 5, 0, 1, 2, 3, 0,
    1, 2, 0, 1], [.commute 7, .commute 6, .braid 7, .commute 9, .commute 10, .commute 11,
    .commute 5, .commute 6, .braid 7, .commute 9, .commute 10, .braid 11, .commute 13, .commute
    14, .commute 15, .square 16, .commute 4, .commute 5, .commute 6, .braid 7, .commute 9,
    .commute 10, .braid 11, .commute 13, .commute 9, .commute 8, .commute 7, .braid 5, .commute
    1, .braid 2, .braid 0, .commute 2, .braid 3, .commute 5, .braid 1, .commute 3, .commute 4,
    .commute 0, .braid 1, .commute 3])
,
  ([6, 5, 0, 8, 5, 6, 5, 0, 1, 2, 3, 0, 1, 2, 0, 1, 2], [6, 5, 0, 8, 5, 6, 5, 0, 1, 2, 3, 1, 2,
    0, 1], [.commute 13, .braid 11, .braid 13, .square 15, .commute 12])
,
  ([6, 5, 0, 8, 5, 6, 5, 0, 1, 2, 3, 1, 2, 0, 1, 6], [6, 5, 0, 8, 6, 5, 0, 1, 2, 3, 1, 2, 0, 1],
    [.braid 4, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .commute 11,
    .commute 12, .commute 13, .square 14])
,
  ([6, 5, 0, 8, 6, 5, 0, 1, 2, 3, 1, 2, 0, 1, 0], [6, 5, 0, 8, 6, 5, 0, 1, 2, 3, 1, 2, 0, 1, 0],
    [])
,
  ([6, 5, 0, 8, 6, 5, 0, 1, 2, 3, 1, 2, 0, 1, 0, 1], [6, 5, 0, 8, 6, 5, 0, 1, 2, 3, 1, 2, 1, 0],
    [.braid 12, .square 14])
,
  ([6, 5, 0, 8, 6, 5, 0, 1, 2, 3, 1, 2, 1, 0, 8], [5, 6, 0, 5, 3, 2, 1, 0, 8, 0, 1, 2, 3, 2, 0],
    [.commute 3, .commute 4, .commute 2, .braid 0, .braid 2, .braid 4, .commute 6, .commute 7,
    .commute 8, .commute 9, .commute 10, .commute 11, .braid 12, .braid 9, .commute 11, .commute
    12, .braid 7, .commute 9, .commute 10, .commute 11, .commute 6, .braid 7, .commute 9,
    .commute 10, .commute 5, .commute 6, .braid 7, .commute 9, .commute 4, .commute 5, .commute
    6, .braid 7])
,
  ([5, 6, 0, 5, 3, 2, 1, 0, 8, 0, 1, 2, 3, 2, 0, 5], [5, 6, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 1, 2,
    3, 2], [.commute 13, .commute 14, .commute 12, .commute 13, .commute 11, .commute 12, .braid
    9, .commute 11])
,
  ([5, 6, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 1, 2, 3, 2, 2], [5, 6, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 1,
    2, 3], [.square 15])
,
  ([5, 6, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 1, 2, 3, 6], [5, 6, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 1,
    2, 3], [.commute 14, .commute 13, .commute 12])
,
  ([5, 6, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 1, 2, 3, 0], [5, 6, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6,
    1, 2, 3, 0], [])
,
  ([5, 6, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 1, 2, 3, 0, 5], [5, 6, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5,
    6, 1, 0, 5, 2, 3], [.commute 15, .commute 16, .commute 14, .commute 15])
,
  ([5, 6, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 1, 0, 5, 2, 3, 6], [5, 6, 0, 5, 3, 2, 1, 0, 8, 0, 5,
    6, 1, 0, 5, 2, 3], [.commute 12, .commute 13, .commute 11, .braid 9, .braid 11, .braid 13,
    .commute 15, .commute 16, .square 17, .commute 12, .commute 10, .commute 11])
,
  ([5, 6, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 3, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5,
    6, 1, 0, 5, 2, 3, 1, 2, 0], [5, 6, 0, 5, 3, 2, 1, 6, 3, 2, 0, 5, 8, 0, 1, 2, 0, 8, 5, 0, 5,
    6, 1, 0, 5, 2, 3, 1, 2, 0], [.commute 14, .commute 15, .commute 13, .commute 14, .braid 15,
    .square 17, .commute 11, .commute 12, .commute 13, .commute 10, .commute 11, .commute 12,
    .braid 13, .commute 15, .square 16, .commute 12, .commute 13, .commute 14, .commute 11,
    .commute 12, .commute 13, .braid 14, .commute 16, .commute 17, .commute 18, .square 19,
    .commute 13, .commute 14, .braid 15, .commute 17, .commute 10, .commute 11, .commute 12,
    .braid 13, .commute 15, .commute 16, .braid 17, .square 19, .commute 11, .commute 12,
    .commute 13, .braid 14, .commute 9, .commute 10, .commute 11, .braid 12, .commute 14, .braid
    15, .commute 17, .square 18, .braid 13, .commute 15, .commute 16, .commute 17, .commute 12,
    .braid 13, .commute 15, .commute 8, .commute 9, .commute 10, .commute 11, .commute 7,
    .commute 8, .commute 9])
,
  ([5, 6, 0, 5, 3, 2, 1, 6, 3, 2, 0, 5, 8, 0, 1, 2, 0, 8, 5, 0, 5, 6, 1, 0, 5, 2, 3, 1, 2, 0],
    [3, 0, 5, 6, 2, 3, 1, 2, 0, 1, 5, 0, 8, 0, 5, 6, 1, 0, 2, 1, 5, 2, 3, 1, 2, 0], [.commute 3,
    .commute 4, .commute 5, .commute 1, .commute 2, .commute 3, .commute 4, .braid 5, .commute
    7, .commute 8, .braid 9, .braid 11, .commute 13, .commute 14, .braid 15, .braid 17, .square
    19, .commute 18, .commute 8, .commute 9, .commute 10, .commute 11, .braid 12, .commute 4,
    .commute 5, .commute 6, .commute 1, .commute 2, .commute 0, .commute 1, .braid 2, .commute
    4, .commute 5, .braid 6, .commute 8, .commute 9, .braid 10, .commute 12, .braid 13, .commute
    15, .commute 16, .commute 17, .braid 18, .square 20, .braid 11, .commute 13, .commute 14,
    .commute 15, .commute 16, .commute 17, .commute 10, .braid 11, .commute 13, .commute 14,
    .commute 15, .commute 9, .commute 10, .braid 11, .commute 8, .commute 9, .commute 7,
    .commute 1, .commute 2, .commute 3])
,
  ([3, 0, 5, 6, 2, 3, 1, 2, 0, 1, 5, 0, 8, 0, 5, 6, 1, 0, 2, 1, 5, 2, 3, 1, 2, 0], [0, 5, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 3, 2, 0], [.commute 0, .commute 1, .commute 2,
    .braid 3, .braid 5, .braid 7, .braid 9, .commute 11, .braid 12, .commute 14, .braid 15,
    .braid 17, .commute 19, .square 20, .commute 18, .commute 19, .square 20, .commute 17,
    .commute 8, .commute 6, .commute 7, .commute 4, .commute 5, .commute 6])
,
  ([0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 3, 2, 0, 5, 6, 0, 5, 3, 2, 1, 0, 8,
    0, 5, 6, 1, 0, 5, 2, 3], [0, 2, 1, 3, 2, 3, 0, 5, 0, 0, 5, 2, 3], [.commute 17, .commute 18,
    .commute 19, .commute 16, .commute 17, .commute 18, .braid 19, .square 21, .commute 14,
    .commute 15, .commute 16, .commute 17, .commute 13, .commute 14, .commute 15, .commute 16,
    .braid 17, .commute 19, .square 20, .square 19, .square 18, .braid 14, .commute 16, .square
    17, .commute 15, .square 16, .commute 13, .commute 14, .square 15, .commute 12, .commute 13,
    .square 14, .commute 11, .commute 12, .square 13, .commute 10, .commute 11, .square 12,
    .commute 6, .commute 7, .commute 8, .commute 9, .commute 2, .commute 3, .commute 4, .commute
    5, .commute 6, .commute 7, .commute 8, .braid 9, .square 11, .square 10, .commute 7,
    .commute 8, .square 9, .commute 4, .commute 5, .commute 6, .commute 1, .commute 2, .commute
    3, .commute 4, .commute 5, .braid 6])
,
  ([0, 2, 1, 3, 2, 3, 0, 5, 0, 0, 5, 2, 3], [0, 1, 2, 1, 0], [.square 8, .square 7, .braid 3,
    .commute 5, .square 6, .commute 4, .square 5, .braid 1])
,
  ([0, 1, 2, 1, 0], [0, 1, 2, 1, 0], [])
,
  ([0, 1, 2, 1, 0, 0, 1, 2, 1, 0], [], [.square 4, .square 3, .square 2, .square 1, .square 0])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 1, 0, 3], [5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 3,
    1, 0], [.commute 14, .commute 13])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 3, 1, 0, 0], [5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2,
    3, 1], [.square 15])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 0, 5, 2, 3, 1, 5], [5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 2, 3, 0, 1],
    [.commute 11, .commute 12, .commute 13, .square 14, .commute 10, .commute 11])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 2, 3, 0, 1, 1], [5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 2, 3, 0],
    [.square 13])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 6, 1, 2, 3, 0, 8], [6, 5, 0, 8, 5, 6, 5, 1, 2, 3, 1, 0], [.commute
    7, .commute 8, .commute 9, .commute 10, .commute 6, .commute 5, .braid 6, .commute 8,
    .commute 9, .braid 10, .square 12, .commute 4, .commute 5, .braid 6, .commute 8, .commute 9,
    .commute 8, .commute 7, .commute 6, .commute 1, .braid 2, .braid 0, .commute 2, .braid 3,
    .commute 5, .braid 1, .commute 3, .commute 4, .commute 0, .braid 1, .commute 3])
,
  ([6, 5, 0, 8, 5, 6, 5, 1, 2, 3, 1, 0, 2], [6, 5, 0, 8, 5, 6, 5, 1, 2, 3, 1, 2, 0], [.commute
    11])
,
  ([6, 5, 0, 8, 5, 6, 5, 1, 2, 3, 1, 2, 0, 6], [6, 5, 0, 8, 6, 5, 1, 2, 3, 1, 2, 0], [.braid 4,
    .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .square 12])
,
  ([6, 5, 0, 8, 6, 5, 1, 2, 3, 1, 2, 0, 0], [6, 5, 0, 8, 6, 5, 1, 2, 3, 1, 2], [.square 11])
,
  ([6, 5, 0, 8, 6, 5, 1, 2, 3, 1, 2, 1], [6, 5, 0, 8, 6, 5, 1, 2, 3, 1, 2, 1], [])
,
  ([6, 5, 0, 8, 6, 5, 1, 2, 3, 1, 2, 1, 8], [5, 6, 0, 5, 0, 1, 2, 3, 1, 2, 1], [.commute 3,
    .commute 4, .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .square
    11, .commute 2, .braid 0, .braid 2])
,
  ([5, 6, 0, 5, 0, 1, 2, 3, 1, 2, 1, 5], [5, 6, 5, 0, 1, 2, 3, 1, 2, 1], [.braid 2, .commute 4,
    .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .square 10])
,
  ([5, 6, 5, 0, 1, 2, 3, 1, 2, 1, 2], [5, 6, 5, 0, 1, 2, 3, 2, 1], [.braid 7, .square 9])
,
  ([5, 6, 5, 0, 1, 2, 3, 2, 1, 6], [6, 5, 0, 1, 2, 3, 2, 1], [.braid 0, .commute 2, .commute 3,
    .commute 4, .commute 5, .commute 6, .commute 7, .square 8])
,
  ([6, 5, 0, 1, 2, 3, 2, 1, 0], [6, 5, 0, 1, 2, 3, 2, 1, 0], [])
,
  ([6, 5, 0, 1, 2, 3, 2, 1, 0, 5], [6, 3, 2, 1, 0, 5, 0, 1, 2, 3], [.braid 4, .commute 6,
    .commute 7, .commute 8, .commute 3, .braid 4, .commute 6, .commute 7, .commute 2, .commute
    3, .braid 4, .commute 6, .commute 1, .commute 2, .commute 3, .braid 4])
,
  ([6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 6], [3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3], [.commute 9, .commute
    8, .commute 7, .commute 6, .commute 0, .commute 1, .commute 2, .commute 3, .braid 4])
,
  ([3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3, 0, 1, 2, 1, 0], [3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3, 0, 1, 2,
    1, 0], [])
,
  ([3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3, 0, 1, 2, 1, 0, 0, 1, 2, 1, 0], [3, 2, 1, 0, 5, 6, 5, 0, 1,
    2, 3], [.square 15, .square 14, .square 13, .square 12, .square 11])
,
  ([3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3, 5, 6, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 3], [5, 0,
    8, 3, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3], [.braid 4, .commute 6, .commute 7, .commute 8,
    .commute 9, .commute 3, .braid 4, .commute 6, .commute 7, .commute 8, .braid 9, .square 11,
    .commute 2, .commute 3, .braid 4, .commute 6, .commute 7, .commute 8, .braid 9, .square 11,
    .commute 7, .commute 8, .commute 9, .square 10, .commute 6, .commute 7, .commute 8, .square
    9, .commute 5, .commute 6, .commute 4, .braid 2, .braid 4, .braid 6, .square 8, .square 7,
    .commute 5, .commute 6, .braid 7, .commute 9, .braid 10, .commute 12, .commute 3, .commute
    4, .commute 5, .commute 6, .braid 7, .commute 9, .braid 10, .commute 4, .commute 1, .commute
    2, .commute 3, .commute 0, .commute 1, .commute 2])
,
  ([5, 0, 8, 3, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 3, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3], [5, 0, 8,
    0, 5], [.square 15, .square 14, .square 13, .square 12, .square 11, .commute 8, .commute 9,
    .square 10, .commute 7, .braid 5, .braid 7, .square 9, .square 8, .commute 6, .square 7,
    .commute 4, .commute 5, .square 6, .commute 3, .commute 4, .square 5])
,
  ([5, 0, 8, 0, 5], [5, 0, 8, 0, 5], [])
,
  ([5, 0, 8, 0, 5, 0, 1, 2, 1, 0], [5, 0, 8, 0, 5, 0, 1, 2, 1, 0], [])
,
  ([5, 0, 8, 0, 5, 0, 1, 2, 1, 0, 5, 0, 8, 0, 5], [0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0], [.braid 3,
    .commute 5, .commute 6, .commute 7, .braid 8, .square 10, .commute 9, .commute 2, .braid 0,
    .braid 2, .commute 4, .commute 5, .commute 6, .braid 7, .braid 9, .square 11, .braid 4,
    .commute 6, .commute 7, .commute 8, .commute 3, .braid 4, .commute 6, .commute 7, .commute
    2, .commute 3, .braid 4])
,
  ([0, 2, 1, 5, 0, 8, 0, 1, 2, 5, 0], [0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0], [.commute 8, .commute
    7, .commute 2, .commute 1])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 5, 0, 8, 0, 5], [5, 0, 8, 0, 5, 0, 1, 2, 1, 0], [.commute
    7, .commute 8, .braid 9, .square 11, .braid 4, .commute 6, .commute 7, .commute 3, .braid 4,
    .commute 6, .braid 7, .commute 9, .square 10, .braid 8, .square 10, .commute 2, .commute 3,
    .braid 4, .commute 6, .commute 7, .commute 5, .commute 6, .commute 4, .commute 5, .braid 2,
    .braid 0, .commute 2, .braid 3])
,
  ([0, 1, 2, 1, 0, 5, 0, 8, 0, 5], [0, 5, 2, 1, 0, 8, 0, 5, 2, 0], [.braid 4, .commute 6, .braid
    7, .braid 1, .commute 3, .commute 4, .commute 5, .commute 6, .commute 7, .commute 2,
    .commute 1])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 2, 0, 5, 0, 8, 0, 5], [0, 1, 2, 1, 0], [.commute 7, .commute 6,
    .braid 7, .square 9, .square 8, .commute 5, .commute 6, .square 7, .commute 4, .commute 1,
    .commute 2, .commute 3, .braid 4, .square 6, .square 5, .braid 1])
,
  ([5, 0, 8, 0, 5, 5, 0, 8, 0, 5], [], [.square 4, .square 3, .square 2, .square 1, .square 0])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0], [0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0], [])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0], [], [.square 10, .commute
    7, .commute 8, .square 9, .square 8, .square 7, .square 6, .square 5, .square 4, .commute 1,
    .commute 2, .square 3, .square 2, .square 1, .square 0])
,
  ([6, 5, 0, 8, 6, 5, 2, 1, 0, 3], [6, 5, 0, 8, 6, 5, 2, 3, 1, 0], [.commute 8, .commute 7])
,
  ([6, 5, 0, 8, 6, 5, 2, 3, 1, 0, 0], [6, 5, 0, 8, 6, 5, 2, 3, 1], [.square 9])
,
  ([6, 5, 0, 8, 6, 5, 2, 3, 1, 1], [6, 5, 0, 8, 6, 5, 2, 3], [.square 8])
,
  ([6, 5, 0, 8, 6, 5, 2, 3, 8], [5, 6, 0, 5, 2, 3, 0], [.commute 3, .commute 4, .commute 5,
    .commute 6, .square 7, .commute 2, .braid 0, .braid 2, .commute 4, .commute 5])
,
  ([5, 6, 0, 5, 2, 3, 0, 5], [5, 6, 5, 2, 3, 0], [.commute 3, .commute 4, .commute 2, .commute
    3, .braid 4, .square 6, .commute 3, .commute 2])
,
  ([5, 6, 5, 2, 3, 0, 2], [5, 6, 5, 2, 3, 2, 0], [.commute 5])
,
  ([5, 6, 5, 2, 3, 2, 0, 6], [6, 5, 2, 3, 2, 0], [.braid 0, .commute 2, .commute 3, .commute 4,
    .commute 5, .square 6])
,
  ([6, 5, 2, 3, 2, 0, 0], [6, 5, 2, 3, 2], [.square 5])
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
