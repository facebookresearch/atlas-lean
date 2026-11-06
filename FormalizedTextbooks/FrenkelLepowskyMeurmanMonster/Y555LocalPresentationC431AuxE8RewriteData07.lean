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
/-- Exact bounded chunks of literal E8 square, commutation and braid moves, block 7. -/
def y431AuxE8RewriteData07 : Fin 64 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
![
  ([0, 1, 1], [0], [.square 1])
,
  ([5, 1, 0, 8, 0, 5, 1, 0, 1, 0], [5, 1, 0, 8, 0, 5, 0, 1], [.braid 6, .square 8])
,
  ([0, 8, 0, 0, 1, 0], [0, 8, 1, 0], [.square 2])
,
  ([8, 5, 1, 0, 8, 0, 5, 1], [5, 1, 0, 8, 5, 1], [.commute 0, .commute 1, .braid 2, .square 4])
,
  ([5, 1, 0, 8, 5, 1, 0, 8, 0], [0, 5, 1, 0, 8, 5, 1], [.commute 3, .commute 4, .braid 5,
    .square 7, .commute 0, .braid 1, .braid 3, .commute 5, .commute 2, .braid 0, .braid 2,
    .commute 4, .commute 1])
,
  ([0, 5, 1, 0, 8, 5, 1, 6], [0, 5, 1, 0, 8, 5, 6, 1], [.commute 6])
,
  ([0, 5, 1, 0, 8, 5, 6, 1, 0, 1, 0], [0, 5, 1, 0, 8, 5, 6, 0, 1], [.braid 7, .square 9])
,
  ([0, 5, 1, 0, 8, 5, 6, 0, 1, 8, 0, 1, 0], [1, 0, 8, 5, 6], [.commute 4, .commute 5, .commute
    1, .braid 2, .commute 4, .braid 5, .commute 7, .square 8, .braid 0, .commute 2, .commute 3,
    .commute 4, .braid 5, .square 7, .square 6, .square 5, .commute 3, .commute 2])
,
  ([1, 0, 8, 5, 6, 1, 0, 8, 0, 1], [0, 5, 1, 0, 8, 5, 6, 1], [.commute 2, .commute 3, .commute
    4, .braid 5, .square 7, .commute 3, .commute 4, .commute 5, .commute 2, .braid 0, .braid 2,
    .commute 4, .commute 1])
,
  ([0, 5, 1, 0, 8, 5, 6, 1, 1, 0, 8, 0, 1], [1, 0, 8, 5, 6], [.square 7, .commute 4, .commute 5,
    .commute 1, .braid 2, .commute 4, .braid 5, .square 7, .square 6, .braid 0, .commute 2,
    .commute 3, .commute 4, .square 5, .commute 3, .commute 2])
,
  ([1, 0, 8, 5, 6, 1, 2, 1], [1, 0, 8, 5, 6, 1, 2, 1], [])
,
  ([1, 0, 8, 5, 6, 1, 2, 1, 0, 1, 0], [1, 0, 8, 5, 6, 1, 2, 0, 1], [.braid 7, .square 9])
,
  ([1, 0, 8, 5, 6, 1, 2, 0, 1, 0, 1, 0], [1, 0, 8, 5, 6, 1, 2, 1], [.braid 7, .square 9, .square
    8])
,
  ([1, 0, 8, 5, 6, 1, 2, 0, 1, 0, 8, 0], [1, 0, 5, 2, 1, 0, 8, 6, 2, 0, 1, 0], [.braid 7,
    .commute 9, .commute 2, .commute 3, .commute 4, .commute 5, .commute 6, .braid 7, .braid 4,
    .commute 6, .commute 7, .commute 3, .commute 4, .commute 5, .commute 6])
,
  ([1, 0, 5, 2, 1, 0, 8, 6, 2, 0, 1, 0, 5, 1, 0, 8, 0, 5, 0, 1], [0, 5, 6, 1, 0, 5, 2, 1, 0, 8,
    6, 1], [.braid 9, .commute 11, .square 12, .commute 6, .commute 7, .commute 8, .commute 5,
    .commute 6, .commute 4, .commute 3, .braid 4, .braid 6, .braid 8, .commute 10, .braid 11,
    .square 13, .braid 9, .commute 11, .square 12, .commute 8, .braid 9, .square 11, .commute 3,
    .commute 4, .commute 5, .commute 6, .commute 2, .commute 3, .braid 0, .commute 2, .braid 3,
    .commute 5, .braid 6, .commute 8, .commute 9, .commute 5, .commute 6, .commute 2, .commute
    3, .commute 4, .commute 5, .commute 3, .commute 1, .commute 2])
,
  ([0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 5, 1, 0, 8, 0, 5, 1], [1, 0, 5, 2, 1, 0, 8, 6, 2],
    [.commute 11, .square 12, .commute 9, .commute 10, .commute 8, .commute 5, .commute 6,
    .commute 2, .commute 3, .commute 4, .commute 5, .braid 6, .braid 8, .braid 10, .square 12,
    .square 11, .commute 9, .square 10, .commute 5, .commute 6, .commute 3, .commute 1, .commute
    2, .braid 3, .commute 5, .braid 6, .commute 8, .square 9, .commute 2, .commute 3, .commute
    4, .braid 0, .commute 2, .commute 3, .braid 4, .commute 6, .commute 7, .commute 3, .commute
    4, .commute 5, .commute 6])
,
  ([1, 0, 5, 2, 1, 0, 8, 6, 2, 1, 2, 1], [1, 0, 5, 2, 1, 0, 8, 6, 1, 2], [.braid 8, .square 10])
,
  ([1, 0, 5, 2, 1, 0, 8, 6, 1, 2, 1, 2, 1], [1, 0, 5, 2, 1, 0, 8, 6, 2], [.braid 8, .square 10,
    .square 9])
,
  ([1, 0, 5, 2, 1, 0, 8, 6, 2, 1, 0, 5, 0, 1], [1, 0, 5, 2, 1, 0, 8, 6, 2, 1, 0, 5, 0, 1], [])
,
  ([1, 0, 5, 2, 1, 0, 8, 6, 2, 1, 0, 5, 0, 1, 0, 1, 0], [1, 0, 5, 2, 1, 0, 8, 6, 2, 1, 0, 5, 1],
    [.braid 12, .square 14, .square 13])
,
  ([1, 0, 5, 2, 1, 0, 8, 6, 2, 1, 0, 5, 1, 5, 1, 0, 8, 0, 5, 1], [1, 0, 5, 6, 1, 0, 5, 2],
    [.commute 11, .square 12, .square 11, .square 10, .commute 6, .commute 7, .commute 8,
    .square 9, .commute 5, .commute 6, .commute 4, .commute 3, .braid 4, .braid 6, .square 8,
    .commute 7, .square 8, .commute 5, .commute 6])
,
  ([1, 0, 5, 6, 1, 0, 5, 2, 2, 1, 0, 8, 0, 1, 2], [5, 6, 0, 5, 1, 0, 8, 5, 6, 5, 0, 1, 2],
    [.square 7, .commute 6, .braid 4, .braid 6, .commute 8, .commute 3, .commute 4, .braid 1,
    .commute 3, .braid 4, .commute 6, .commute 7, .commute 0, .braid 1, .commute 3, .braid 4,
    .commute 6, .commute 2, .commute 3, .commute 1])
,
  ([5, 6, 0, 5, 1, 0, 8, 5, 6, 5, 0, 1, 2, 1, 2, 1], [5, 6, 0, 5, 1, 0, 8, 5, 6, 5, 2, 0],
    [.braid 11, .square 13, .square 12, .commute 10])
,
  ([5, 6, 0, 5, 1, 0, 8, 5, 6, 5, 2, 0, 1, 2, 1], [5, 6, 0, 5, 1, 0, 8, 5, 6, 5, 0, 1, 2],
    [.commute 10, .braid 11, .square 13])
,
  ([5, 6, 0, 5, 1, 0, 8, 5, 6, 5, 0, 1, 2, 5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8,
    2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0], [5, 6, 1, 8, 0, 5, 1, 0, 8, 6, 5, 2, 1, 0, 1, 8, 1,
    0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0], [.commute 12, .commute 13, .commute 14, .commute 15,
    .square 16, .commute 11, .commute 12, .braid 9, .commute 11, .braid 12, .commute 14, .square
    15, .commute 8, .braid 9, .commute 11, .braid 12, .square 14, .commute 13, .commute 6,
    .commute 3, .braid 4, .braid 6, .commute 8, .commute 9, .commute 10, .braid 11, .braid 13,
    .square 15, .commute 9, .commute 10, .commute 11, .commute 8, .braid 2, .commute 4, .commute
    5, .braid 6, .braid 8, .commute 10, .braid 11, .commute 13, .square 14, .commute 7, .commute
    4, .braid 5, .braid 7, .commute 9, .commute 10, .commute 11, .braid 12, .square 14, .braid
    3, .commute 5, .commute 6, .braid 7, .commute 9, .braid 10, .commute 12, .square 13, .braid
    12, .commute 14, .commute 15, .square 16, .commute 11, .braid 12])
,
  ([5, 6, 1, 8, 0, 5, 1, 0, 8, 6, 5, 2, 1, 0, 1, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0], [8, 0,
    5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 1, 2, 1, 0], [.commute 14, .square 15, .commute 8,
    .commute 9, .commute 10, .commute 11, .braid 12, .square 14, .commute 7, .commute 5,
    .commute 1, .commute 2, .commute 3, .commute 4, .braid 5, .braid 7, .commute 9, .braid 10,
    .commute 12, .commute 13, .commute 14, .commute 4, .commute 5, .commute 0, .commute 1,
    .braid 2, .commute 4, .braid 5, .commute 7, .braid 8, .commute 10, .commute 11, .commute 12,
    .commute 13, .braid 14, .square 16, .commute 4, .commute 5, .commute 3, .commute 0, .braid
    1, .braid 3, .braid 5, .commute 7, .commute 8, .commute 9, .commute 10, .braid 11, .commute
    13, .commute 14, .braid 15, .square 17, .commute 14, .commute 15, .braid 16, .commute 4,
    .commute 2, .commute 3])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 1, 2, 1, 0, 0], [8, 0, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 5, 6, 1, 0, 5, 1, 2, 1], [.square 19])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 1, 2, 1, 2], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0,
    8, 5, 6, 1, 0, 5, 2, 1], [.braid 16, .square 18])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 5], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8,
    5, 6, 1, 2, 0, 1], [.commute 15, .commute 16, .square 17, .commute 14])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 2, 0, 1, 6], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5,
    1, 2, 0, 1], [.commute 12, .commute 13, .commute 14, .commute 15, .square 16])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 1, 2, 0, 1, 1], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 1,
    2, 0], [.square 15])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 1, 2, 0, 0], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 1, 2],
    [.square 14])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 1, 2, 5], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 2],
    [.commute 11, .commute 12, .square 13])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 2, 2], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1], [.square
    12])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 6], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1], [.commute
    11])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 1, 8], [8, 1, 0, 5, 6, 1, 0, 5, 2, 0, 1, 0], [.commute
    10, .commute 11, .square 12, .commute 9, .commute 8, .braid 9, .commute 7, .commute 3,
    .commute 4, .braid 5, .commute 2, .braid 3, .commute 5, .braid 1, .commute 3, .commute 4])
,
  ([8, 1, 0, 5, 6, 1, 0, 5, 2, 0, 1, 0, 0], [8, 1, 0, 5, 6, 1, 0, 5, 2, 0, 1], [.square 11])
,
  ([8, 1, 0, 5, 6, 1, 0, 5, 2, 0, 1, 5], [8, 1, 0, 5, 6, 5, 1, 2, 0, 1], [.commute 7, .commute
    6, .braid 7, .commute 9, .square 10, .commute 6, .commute 5])
,
  ([8, 1, 0, 5, 6, 5, 1, 2, 0, 1, 6], [8, 6, 1, 0, 5, 1, 2, 0, 1], [.braid 3, .commute 5,
    .commute 6, .commute 7, .commute 8, .square 9, .commute 2, .commute 1])
,
  ([8, 6, 1, 0, 5, 1, 2, 0, 1, 1], [8, 6, 1, 0, 5, 1, 2, 0], [.square 8])
,
  ([8, 6, 1, 0, 5, 1, 2, 0, 0], [8, 6, 1, 0, 5, 1, 2], [.square 7])
,
  ([8, 6, 1, 0, 5, 1, 2, 2], [8, 6, 1, 0, 5, 1], [.square 6])
,
  ([8, 6, 1, 0, 5, 1, 5], [8, 6, 0, 1, 0], [.commute 4, .square 5, .braid 2])
,
  ([8, 6, 0, 1, 0, 6], [8, 0, 1, 0], [.commute 1, .commute 2, .commute 3, .square 4])
,
  ([0, 1, 8, 0], [0, 8, 1, 0], [.commute 1])
,
  ([0, 8, 1, 0, 8, 0, 1, 0], [1, 0, 8, 0], [.commute 1, .braid 2, .square 4, .braid 0, .commute
    2, .square 3])
,
  ([0, 8, 0, 1], [0, 8, 0, 1], [])
,
  ([1, 0, 8, 0, 3], [1, 0, 8, 3, 0], [.commute 3])
,
  ([1, 0, 8, 3, 0, 0, 8, 0, 1], [3], [.square 4, .commute 2, .square 3, .commute 1, .square 2,
    .commute 0, .square 1])
,
  ([1, 2, 1, 6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6], [1, 6, 5, 0, 8, 1, 2, 0, 1, 3, 2, 5, 0, 8, 5, 1, 0, 5, 6, 5, 0, 1, 8, 0, 5,
    2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 1], [.braid 18, .commute 20, .commute 21, .commute 22,
    .commute 14, .commute 15, .commute 16, .commute 17, .braid 18, .commute 20, .commute 16,
    .commute 13, .commute 14, .commute 6, .commute 2, .commute 3, .braid 4, .braid 6, .commute
    8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .braid 14, .braid 16,
    .commute 18, .commute 19, .braid 20, .braid 22, .commute 24, .commute 25, .commute 26,
    .braid 27, .commute 29, .commute 30, .braid 31, .commute 33, .commute 34, .commute 9,
    .commute 10, .commute 11, .commute 12, .commute 13, .commute 14, .commute 15, .commute 16,
    .braid 17, .commute 8, .commute 9, .commute 10, .commute 11, .commute 7, .commute 5,
    .commute 1, .commute 2, .commute 3, .commute 4, .braid 5, .braid 7, .commute 9, .commute 10,
    .braid 11, .commute 13])
,
  ([1, 6, 5, 0, 8, 1, 2, 0, 1, 3, 2, 5, 0, 8, 5, 1, 0, 5, 6, 5, 0, 1, 8, 0, 5, 2, 1, 0, 8, 3, 2,
    1, 0, 5, 6, 1], [6, 5, 0, 1, 2, 8, 0, 1, 5, 6, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 3, 2, 1, 0, 5, 6, 1, 2, 1], [.commute 14, .braid 15, .commute 17, .braid 18, .commute
    20, .commute 21, .braid 22, .commute 24, .braid 25, .commute 27, .commute 28, .braid 29,
    .commute 31, .commute 32, .commute 33, .commute 4, .commute 5, .commute 0, .commute 1,
    .braid 2, .commute 4, .braid 5, .commute 7, .commute 8, .commute 9, .commute 10, .braid 11,
    .braid 13, .commute 15, .commute 16, .commute 17, .braid 18, .braid 20, .commute 22,
    .commute 23, .commute 24, .braid 25, .commute 27, .commute 28, .braid 29, .commute 31,
    .commute 32, .commute 19, .braid 15, .commute 17, .commute 18, .commute 14, .braid 15,
    .commute 17, .commute 12, .commute 13, .commute 14, .braid 15, .commute 12, .commute 13,
    .commute 9, .commute 10, .commute 11, .commute 12, .commute 8, .commute 9, .commute 10,
    .commute 11, .commute 9])
,
  ([6, 5, 0, 1, 2, 8, 0, 1, 5, 6, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0,
    5, 6, 1, 2, 1], [6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 3, 2, 1, 0, 5, 6, 1, 2, 1], [.commute 7, .commute 8, .commute 4, .commute 5, .commute
    6, .commute 7, .commute 3])
,
  ([6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0,
    5, 6, 1, 2, 1, 1, 2, 1], [6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0,
    5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [.square 35, .square 34, .square 33])
,
  ([1, 3], [3, 1], [.commute 0])
,
  ([3, 1, 1], [3], [.square 1])
,
  ([8, 1, 0, 8, 0, 1], [1, 0, 8, 1], [.commute 0, .braid 1, .square 3])
,
  ([8, 1, 0, 8, 1], [1, 0, 8, 0, 1], [.commute 0, .braid 1])
,
  ([5, 1, 0, 8, 0, 5, 1, 6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2,
    1, 0, 8, 3, 2, 1, 0, 5, 6], [5, 1, 0, 8, 0, 6, 5, 0, 1, 8, 0, 5, 6, 2, 1, 3, 2, 0, 5, 8, 0,
    1, 0, 8, 5, 0, 5, 6, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 1], [.braid 22, .commute 24, .commute
    25, .commute 26, .commute 18, .commute 19, .commute 20, .commute 21, .braid 22, .commute 24,
    .commute 20, .commute 17, .commute 18, .commute 10, .commute 6, .commute 7, .braid 8, .braid
    10, .commute 12, .commute 13, .commute 14, .commute 15, .commute 16, .commute 17, .braid 18,
    .braid 20, .commute 22, .commute 23, .braid 24, .braid 26, .commute 28, .commute 29,
    .commute 30, .braid 31, .commute 33, .commute 34, .braid 35, .commute 37, .commute 38,
    .commute 23, .commute 24, .commute 25, .commute 26, .braid 21, .commute 23, .commute 24,
    .commute 20, .braid 21, .commute 19, .braid 5, .commute 7, .commute 8, .commute 9, .commute
    10, .braid 11, .commute 13, .commute 14, .commute 15, .commute 16, .braid 17, .braid 19,
    .commute 21, .braid 22, .braid 24])
,
  ([5, 1, 0, 8, 0, 6, 5, 0, 1, 8, 0, 5, 6, 2, 1, 3, 2, 0, 5, 8, 0, 1, 0, 8, 5, 0, 5, 6, 5, 2, 1,
    0, 8, 3, 2, 1, 0, 5, 6, 1], [5, 1, 0, 6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 2, 8, 3, 2, 1, 0,
    8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 5, 1], [.braid 26, .commute 28, .commute
    29, .commute 30, .commute 31, .commute 32, .commute 33, .commute 34, .commute 35, .braid 36,
    .commute 27, .commute 28, .commute 25, .commute 26, .braid 20, .commute 22, .commute 23,
    .commute 24, .commute 16, .commute 17, .commute 18, .commute 14, .commute 4, .braid 5,
    .commute 7, .commute 8, .braid 9, .commute 11, .commute 12, .commute 13, .braid 14, .commute
    16, .commute 17, .braid 18, .commute 20, .commute 21, .commute 22, .commute 23, .braid 24,
    .braid 26, .braid 28, .commute 30, .commute 31, .commute 32, .commute 33, .braid 34,
    .commute 36, .commute 27, .commute 25, .commute 26, .commute 13, .commute 14, .commute 15,
    .commute 16, .commute 7, .commute 3, .commute 4, .braid 5, .braid 7, .commute 9, .commute
    10, .braid 11, .commute 13, .commute 14])
,
  ([5, 1, 0, 6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 2, 8, 3, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8,
    3, 2, 1, 0, 5, 6, 0, 5, 1], [6, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 0, 5, 1], [.commute 15, .braid 16, .commute
    18, .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .commute
    25, .commute 2, .braid 3, .commute 5, .commute 6, .braid 7, .commute 9, .commute 10, .braid
    11, .commute 13, .commute 14, .commute 15, .braid 16, .commute 18, .commute 19, .commute 20,
    .commute 21, .commute 14, .commute 15, .commute 16, .braid 17, .commute 0, .braid 1,
    .commute 3, .commute 4, .commute 5, .commute 6, .braid 7, .commute 9, .commute 10, .braid
    11, .commute 13, .commute 14, .braid 15, .commute 17, .commute 0, .commute 1])
,
  ([6, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    3, 2, 1, 0, 5, 6, 0, 5, 1, 5, 1, 0, 8, 0, 5, 1], [6, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3,
    2, 8, 0, 1, 2, 0, 3, 5, 8, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5, 6, 1], [.commute 38, .square 39,
    .square 38, .square 37, .commute 30, .commute 31, .commute 32, .commute 29, .commute 30,
    .commute 28, .braid 26, .braid 28, .braid 30, .braid 32, .commute 34, .commute 35, .square
    36, .commute 25, .commute 26, .commute 27, .commute 28, .commute 24, .commute 25, .braid 22,
    .commute 24, .braid 25, .commute 27, .braid 28, .commute 30, .commute 31, .braid 32,
    .commute 34, .square 35, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25,
    .commute 26, .commute 20, .commute 21, .commute 22, .braid 18, .commute 20, .commute 21,
    .braid 22, .commute 24, .commute 25, .braid 26, .commute 28, .commute 29, .commute 30,
    .commute 31, .braid 32, .square 34, .commute 29, .braid 16, .commute 18, .commute 19,
    .commute 20, .commute 21, .commute 15, .braid 16, .commute 18])
,
  ([6, 5, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 8, 0, 1, 2, 0, 3, 5, 8, 0, 1, 2, 6, 5, 0, 8, 1,
    0, 5, 6, 1], [6, 5, 0, 1, 8, 0, 5, 6, 2, 1, 0, 3, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0,
    8, 3, 2, 1, 0, 5, 6], [.commute 19, .commute 12, .commute 13, .commute 14, .commute 11,
    .commute 12, .commute 4, .braid 2, .braid 4, .commute 6, .commute 7, .commute 8, .commute 9,
    .commute 10, .commute 11, .braid 12, .braid 14, .commute 16, .commute 17, .commute 18,
    .braid 19, .braid 21, .commute 23, .commute 24, .commute 25, .commute 26, .braid 27, .braid
    29, .commute 31, .commute 32, .square 33, .commute 24, .commute 25, .commute 26, .commute
    27, .commute 18, .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute
    24, .commute 25, .commute 26, .commute 22, .commute 23, .commute 17, .commute 18, .commute
    19, .commute 20, .commute 21, .commute 22, .commute 20, .braid 15, .commute 17, .commute 18,
    .commute 19, .commute 17, .commute 13, .commute 14, .braid 15, .commute 11, .commute 12,
    .commute 10])
,
  ([6, 5, 0, 1, 8, 0, 5, 6, 2, 1, 0, 3, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0,
    5, 6], [6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6], [.commute 11, .commute 3])
,
  ([1, 0, 8, 0, 1, 4], [1, 0, 8, 4, 0, 1], [.commute 4, .commute 3])
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
