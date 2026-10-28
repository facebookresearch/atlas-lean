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
def y431E8RewriteData04 : Fin 64 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
![
  ([6, 5, 1, 0, 8, 0, 5, 6, 1, 0, 1, 2, 1, 0], [6, 5, 1, 0, 8, 0, 5, 6, 0, 1, 2, 0, 1, 0],
    [.braid 8, .commute 10])
,
  ([6, 5, 1, 0, 8, 0, 5, 6, 0, 1, 2, 0, 1, 0, 6, 5, 1, 0, 8, 0, 5, 6, 1], [6, 1, 0, 5, 2, 1, 0,
    8, 0, 5, 6, 1, 2, 0, 1], [.commute 7, .commute 8, .commute 9, .commute 10, .commute 11,
    .commute 12, .square 13, .braid 10, .commute 12, .square 13, .braid 5, .commute 7, .commute
    8, .commute 9, .braid 10, .square 12, .commute 11, .commute 4, .commute 1, .braid 2, .braid
    4, .commute 6, .commute 7, .commute 8, .braid 9, .braid 11, .square 13, .commute 12, .braid
    6, .commute 8, .commute 9, .commute 10, .commute 11, .commute 5, .braid 6, .commute 8,
    .commute 9, .commute 10, .commute 4, .commute 5, .braid 6])
,
  ([1, 0, 2, 1, 6, 5, 0, 8, 0, 1, 2, 5, 0, 1, 6], [6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 2, 0, 1],
    [.commute 13, .commute 12, .commute 10, .commute 11, .commute 9, .commute 10, .commute 3,
    .commute 4, .commute 2, .commute 3, .commute 1, .commute 0])
,
  ([6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 2, 0, 1, 0, 1, 2, 1, 0], [6, 1, 0, 5, 2, 1, 0, 8, 0, 5,
    6, 2, 0, 1], [.braid 13, .square 15, .braid 11, .commute 13, .square 14, .braid 12, .square
    14])
,
  ([1, 0, 2, 6, 5, 0, 8, 0, 1, 2, 5, 0, 1, 6], [6, 5, 1, 0, 8, 0, 5, 6, 0, 1, 2, 0, 1, 0],
    [.commute 2, .commute 3, .commute 4, .commute 5, .commute 6, .braid 7, .commute 9, .braid
    10, .commute 12, .commute 11, .commute 10, .commute 8, .commute 9, .commute 7, .commute 8,
    .commute 1, .braid 2, .commute 4, .braid 5, .commute 7, .commute 0, .commute 1])
,
  ([6, 5, 1, 0, 8, 0, 5, 6, 0, 1, 2, 0, 1, 0, 0, 1, 2, 1, 0], [6, 5, 1, 0, 8, 0, 5, 6, 1],
    [.square 13, .square 12, .commute 10, .square 11, .braid 8, .square 10, .square 9])
,
  ([6, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0], [6, 5, 1, 0, 8, 0, 5, 6, 1, 0,
    5, 2, 1, 0, 8, 0, 5, 1, 2, 0], [])
,
  ([6, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 1, 2, 0, 6, 5, 1, 0, 8, 0, 5, 6, 1], [1,
    8, 0, 5, 6, 1, 5, 2, 0, 5, 8, 0, 1, 2, 0, 8, 5, 0, 1, 6, 5, 0, 8, 6, 1], [.braid 13,
    .commute 15, .commute 16, .commute 17, .commute 10, .commute 11, .commute 12, .braid 13,
    .commute 11, .commute 9, .braid 3, .commute 5, .commute 6, .commute 7, .commute 8, .braid 9,
    .braid 11, .commute 13, .braid 14, .commute 16, .braid 17, .commute 19, .commute 20,
    .commute 21, .braid 22, .square 24, .commute 20, .commute 18, .commute 8, .commute 9,
    .commute 1, .commute 2, .braid 3, .commute 5, .braid 6, .commute 8, .braid 9, .commute 11,
    .commute 12, .commute 13, .braid 14, .commute 16, .commute 17, .braid 18, .braid 20,
    .commute 22, .square 23, .commute 17, .commute 18, .braid 11, .commute 13, .commute 14,
    .commute 15, .commute 10, .braid 11, .commute 13, .commute 8, .commute 9, .commute 7,
    .commute 0, .commute 1, .commute 2, .braid 3, .commute 5])
,
  ([1, 8, 0, 5, 6, 1, 5, 2, 0, 5, 8, 0, 1, 2, 0, 8, 5, 0, 1, 6, 5, 0, 8, 6, 1], [8, 0, 5, 6, 1,
    0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8], [.commute 6, .braid 7, .braid 9, .commute
    11, .commute 12, .braid 13, .braid 15, .commute 17, .braid 18, .commute 20, .commute 21,
    .square 22, .commute 17, .commute 18, .commute 16, .commute 4, .commute 5, .commute 6,
    .commute 3, .commute 4, .commute 0, .braid 1, .commute 3, .braid 4, .braid 6, .commute 8,
    .commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .braid 14, .braid 16, .braid
    18, .commute 20, .square 21, .commute 11, .commute 12, .commute 13, .commute 14, .commute
    15, .commute 16, .braid 9, .commute 11, .commute 12, .commute 13, .commute 8, .braid 9,
    .commute 3, .commute 4, .commute 5, .commute 6, .commute 4, .commute 2, .commute 3])
,
  ([8, 0, 1, 2, 5, 0, 1, 6, 5, 0, 8, 0, 1, 2, 5, 0, 1, 6, 5, 0, 8], [8, 0, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8], [.commute 16, .commute 17, .commute 13, .commute 14,
    .commute 15, .commute 16, .commute 14, .commute 12, .commute 13, .commute 6, .commute 7,
    .commute 3, .commute 4, .commute 5, .commute 6, .commute 4, .commute 2, .commute 3])
,
  ([8, 1], [8, 1], [])
,
  ([1, 8, 1], [8], [.commute 0, .square 1])
,
  ([1, 6], [6, 1], [.commute 0])
,
  ([6, 1, 1], [6], [.square 1])
,
  ([6, 8], [8, 6], [.commute 0])
,
  ([8, 6, 8], [6], [.commute 0, .square 1])
,
  ([1, 5], [5, 1], [.commute 0])
,
  ([5, 1, 1], [5], [.square 1])
,
  ([5, 8], [8, 5], [.commute 0])
,
  ([8, 5, 8], [5], [.commute 0, .square 1])
,
  ([1, 8], [8, 1], [.commute 0])
,
  ([0, 8, 1], [0, 8, 1], [])
,
  ([1, 8, 0], [8, 1, 0], [.commute 0])
,
  ([8, 1, 0, 8, 1], [1, 0, 8, 0, 1], [.commute 0, .braid 1])
,
  ([1, 0, 8, 0, 1], [1, 0, 8, 0, 1], [])
,
  ([8, 1, 0, 8, 0, 1], [1, 0, 8, 1], [.commute 0, .braid 1, .square 3])
,
  ([1, 8, 0, 1], [8, 0, 1, 0], [.commute 0, .braid 1])
,
  ([8, 0, 1, 0, 1, 0, 8, 0, 1], [0, 1, 0], [.braid 1, .square 3, .square 2, .commute 0, .square
    1, .braid 0])
,
  ([0, 1, 0], [0, 1, 0], [])
,
  ([1, 0], [1, 0], [])
,
  ([1, 0, 1], [0, 1, 0], [.braid 0])
,
  ([1, 0, 8, 1, 0, 1, 0], [1, 0, 8, 0, 1], [.braid 3, .square 5])
,
  ([8, 0, 1, 0], [8, 0, 1, 0], [])
,
  ([8, 0, 1, 0, 8], [1, 0, 8, 0, 1], [.braid 1, .commute 3, .commute 0, .braid 1])
,
  ([1, 0, 8, 0, 1, 8], [8, 0, 1, 0], [.braid 1, .commute 3, .square 4, .commute 0, .braid 1])
,
  ([8, 0, 1, 0, 6], [8, 6, 0, 1, 0], [.commute 3, .commute 2, .commute 1])
,
  ([8, 6, 0, 1, 0, 1], [8, 6, 1, 0], [.braid 2, .square 4])
,
  ([8, 6, 1, 0, 8, 1], [1, 0, 8, 6, 0, 1], [.commute 0, .commute 1, .braid 2, .commute 0,
    .commute 1, .commute 2])
,
  ([1, 0, 8, 6, 0, 1, 5], [1, 0, 8, 6, 0, 5, 1], [.commute 5])
,
  ([1, 0, 8, 6, 0, 5, 1, 0], [1, 0, 8, 6, 0, 5, 1, 0], [])
,
  ([1, 0, 8, 6, 0, 5, 1, 0, 1], [1, 0, 8, 6, 0, 5, 0, 1, 0], [.braid 6])
,
  ([1, 0, 8, 6, 0, 5, 0, 1, 0, 8], [8, 6, 0, 5, 1, 0, 8, 5, 0, 1], [.braid 6, .commute 8,
    .commute 2, .commute 1, .braid 2, .commute 4, .commute 5, .braid 6, .commute 4, .commute 0,
    .commute 1, .braid 2, .braid 4, .commute 6, .commute 3, .commute 0])
,
  ([8, 6, 0, 5, 1, 0, 8, 5, 0, 1, 6], [8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 1], [.commute 9, .commute
    8])
,
  ([8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 1, 5], [8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 5, 1], [.commute 10])
,
  ([8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 5, 1, 2], [8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 5, 1, 2], [])
,
  ([8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 5, 1, 2, 0], [8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 5, 1, 2, 0], [])
,
  ([8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 5, 1, 2, 0, 1], [8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 5, 1, 2, 0, 1],
    [])
,
  ([8, 6, 0, 5, 1, 0, 8, 5, 6, 0, 5, 1, 2, 0, 1, 6], [8, 6, 0, 5, 1, 0, 8, 0, 5, 6, 0, 5, 1, 2,
    0, 1], [.commute 14, .commute 13, .commute 12, .commute 11, .commute 8, .braid 9, .braid 7,
    .commute 9])
,
  ([8, 6, 0, 5, 1, 0, 8, 0, 5, 6, 0, 5, 1, 2, 0, 1, 5], [8, 6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5,
    1, 2, 0, 1], [.commute 15, .commute 11, .commute 12, .braid 13, .commute 12, .commute 13,
    .braid 10, .commute 12])
,
  ([8, 6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 1, 2, 0, 1, 0], [8, 6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0,
    5, 1, 2, 0, 1, 0], [])
,
  ([8, 6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 1, 2, 0, 1, 0, 8], [6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0,
    5, 2, 1, 0, 8, 2, 0, 1], [.braid 15, .commute 17, .braid 5, .commute 7, .commute 8, .commute
    9, .commute 3, .commute 4, .braid 5, .commute 7, .commute 3, .commute 0, .braid 1, .braid 3,
    .commute 5, .commute 6, .braid 7, .braid 9, .commute 11, .commute 12, .commute 13, .commute
    14, .braid 15, .braid 12, .commute 14, .commute 15, .commute 8, .commute 6, .commute 7,
    .braid 4, .commute 6, .commute 2, .commute 3, .braid 4, .commute 2])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 0, 1, 6], [6, 0, 5, 1, 0, 8, 0, 5, 6, 1,
    0, 5, 2, 1, 0, 8, 6, 2, 0, 1], [.commute 18, .commute 17, .commute 16])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 2, 0, 1, 2], [6, 0, 5, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 6, 0, 1, 2, 1], [.commute 17, .braid 18])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 1, 2, 1, 5], [6, 0, 5, 1, 0, 8, 0, 5,
    6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 2, 1], [.commute 20, .commute 19, .commute 18])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 2, 1, 0], [6, 0, 5, 1, 0, 8, 0,
    5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 2, 1, 0], [])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 2, 1, 0, 1], [6, 0, 5, 1, 0, 8,
    0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 2, 0, 1, 0], [.braid 21])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 6, 0, 5, 1, 2, 0, 1, 0, 6], [6, 0, 5, 1, 0,
    8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 1, 2, 0, 1, 0], [.commute 23, .commute 22,
    .commute 21, .commute 20, .commute 19, .commute 16, .braid 17])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 1, 2, 0, 1, 0, 5], [6, 0, 5, 1,
    0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2, 0, 1], [.braid 22, .commute 24,
    .commute 19, .commute 20, .commute 21, .braid 22, .braid 19, .commute 21, .commute 22])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2, 0, 1, 2], [6, 0, 5,
    1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1], [.commute 23,
    .braid 24])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0], [6, 0,
    5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0], [])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0, 6], [6,
    0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 1, 0],
    [.commute 27, .commute 26, .commute 25, .commute 24, .commute 23, .commute 18, .commute 19,
    .commute 20, .braid 21, .commute 17, .commute 18, .braid 19, .commute 21, .commute 16,
    .braid 17, .commute 19, .commute 20])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 1, 0, 5],
    [6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0],
    [.braid 22, .commute 24, .commute 25, .commute 26, .braid 27, .commute 21, .braid 22,
    .commute 24, .braid 25, .commute 27, .braid 23, .commute 25, .commute 26, .commute 22,
    .braid 23, .commute 25, .commute 21, .commute 22, .braid 23])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 1, 0,
    1], [6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0,
    1, 0], [.braid 28])
,
  ([6, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 0, 1, 0,
    8], [0, 1, 8, 0, 5, 6, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 1, 2, 0, 1, 8, 0, 8, 5, 2, 1, 0, 8,
    1, 2, 1], [.braid 28, .commute 30, .braid 26, .commute 28, .commute 29, .commute 25, .braid
    26, .commute 28, .commute 15, .commute 16, .commute 14, .braid 12, .braid 14, .braid 16,
    .commute 18, .commute 19, .commute 20, .commute 21, .commute 11, .commute 12, .braid 9,
    .commute 11, .braid 12, .commute 14, .commute 15, .braid 16, .commute 18, .commute 19,
    .commute 14, .braid 4, .commute 6, .commute 7, .commute 2, .commute 3, .braid 4, .commute 6,
    .braid 7, .commute 9, .commute 10, .commute 11, .braid 12, .braid 14, .commute 16, .commute
    17, .commute 10, .commute 11, .commute 12, .commute 9, .commute 0, .commute 1, .commute 2,
    .commute 3, .braid 4, .commute 6, .braid 7, .braid 9, .commute 11, .braid 12, .commute 14,
    .commute 15, .commute 16, .braid 17, .braid 19, .braid 21])
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
