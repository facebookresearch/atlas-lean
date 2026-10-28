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
def y431E8RewriteData03 : Fin 64 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
![
  ([0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2, 0, 1, 8], [0, 8, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8,
    5, 6, 0, 5, 2, 1], [.commute 16, .commute 14, .commute 15, .braid 12, .commute 14, .braid 5,
    .commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .braid 12, .commute 8,
    .commute 9, .commute 7, .commute 8, .braid 9, .commute 11, .commute 12, .commute 6, .commute
    4, .commute 3, .braid 4, .braid 6, .commute 8, .braid 9, .commute 11, .commute 7, .commute
    8, .commute 5, .commute 6, .commute 7, .commute 2, .commute 3, .commute 4, .commute 5,
    .commute 6, .commute 4, .commute 3, .commute 1])
,
  ([0, 8, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 5, 6, 0, 5, 2, 1, 2], [0, 8, 5, 6, 1, 0, 5, 3, 2, 1, 0,
    8, 5, 6, 0, 5, 1, 2, 1], [.braid 16])
,
  ([0, 8, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 2, 1, 6], [0, 8, 5, 6, 1, 0, 5, 3, 2, 1,
    0, 8, 0, 5, 6, 0, 5, 1, 2, 1], [.commute 18, .commute 17, .commute 16, .commute 13, .braid
    14, .braid 12, .commute 14])
,
  ([0, 8, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 0, 5, 1, 2, 1, 0], [0, 8, 5, 6, 1, 0, 5, 3, 2,
    1, 0, 8, 0, 5, 6, 0, 5, 1, 2, 1, 0], [])
,
  ([0, 8, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 0, 5, 1, 2, 1, 0, 1], [0, 8, 5, 6, 1, 0, 5, 3,
    2, 1, 0, 8, 0, 5, 6, 0, 5, 1, 2, 0, 1, 0], [.braid 19])
,
  ([0, 8, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 0, 5, 1, 2, 0, 1, 0, 8], [0, 8, 5, 3, 2, 1, 0,
    8, 5, 6, 1, 2, 0, 5, 1, 0, 8, 5, 6, 1, 2, 0, 1], [.braid 19, .commute 21, .braid 10,
    .commute 12, .commute 13, .commute 6, .commute 7, .commute 8, .commute 9, .braid 10,
    .commute 12, .braid 13, .commute 15, .commute 16, .commute 17, .commute 18, .braid 19,
    .braid 16, .commute 18, .commute 19, .commute 3, .commute 4, .commute 5, .commute 6,
    .commute 7, .commute 8, .commute 9, .braid 10, .commute 12, .braid 13, .commute 15, .braid
    16, .commute 18, .commute 11, .commute 12, .commute 10, .braid 8, .braid 10, .braid 12,
    .commute 14, .commute 15, .commute 16, .commute 17, .commute 13, .commute 14, .commute 11,
    .commute 12, .commute 4, .commute 5, .braid 6, .commute 8, .commute 9, .commute 10, .commute
    3, .braid 4, .commute 6, .commute 7, .commute 8, .commute 9, .braid 10, .braid 12, .braid
    14, .commute 16, .commute 13])
,
  ([0, 8, 5, 3, 2, 1, 0, 8, 5, 6, 1, 2, 0, 5, 1, 0, 8, 5, 6, 1, 2, 0, 1], [0, 5, 3, 2, 1, 0, 8,
    0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 2, 0, 1], [.commute 11, .commute 12, .commute 1,
    .commute 2, .commute 3, .commute 4, .braid 5])
,
  ([0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 2, 0, 1, 5], [0, 5, 3, 2, 1, 0,
    8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1], [.commute 22, .commute 20, .commute
    21])
,
  ([0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 2], [0, 5, 3, 2, 1,
    0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 1, 2, 1], [.braid 22])
,
  ([0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 1, 2, 1, 6], [0, 5, 3, 2,
    1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 1, 2, 1], [.commute 24, .commute
    23, .commute 22, .commute 18, .commute 19, .braid 20, .commute 17, .braid 18, .commute 20])
,
  ([0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 1, 2, 1, 0], [0, 5, 3,
    2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 1, 2, 1, 0], [])
,
  ([0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 1, 2, 1, 0, 5], [0, 5,
    3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [.commute 22,
    .commute 23, .commute 24, .braid 25, .braid 22, .commute 24, .commute 25, .commute 21,
    .braid 22, .commute 24])
,
  ([0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0, 6], [0,
    5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0],
    [.commute 27, .commute 26, .commute 25, .commute 20, .commute 21, .commute 22, .braid 23,
    .commute 19, .commute 20, .braid 21, .commute 23, .commute 18, .braid 19, .commute 21,
    .commute 22, .braid 17, .commute 19, .commute 20, .commute 21])
,
  ([0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0, 1],
    [0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0, 1],
    [])
,
  ([0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0, 1,
    1], [0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0],
    [.square 29])
,
  ([0, 5], [0, 5], [])
,
  ([0, 5, 2], [0, 5, 2], [])
,
  ([0, 5, 2, 6], [0, 5, 6, 2], [.commute 2])
,
  ([0, 5, 6, 2, 1], [0, 5, 6, 2, 1], [])
,
  ([0, 5, 6, 2, 1, 8], [0, 8, 5, 6, 2, 1], [.commute 4, .commute 3, .commute 2, .commute 1])
,
  ([0, 8, 5, 6, 2, 1, 2], [0, 8, 5, 6, 1, 2, 1], [.braid 4])
,
  ([0, 8, 5, 6, 1, 2, 1, 0], [0, 8, 5, 6, 1, 2, 1, 0], [])
,
  ([0, 8, 5, 6, 1, 2, 1, 0, 5], [0, 8, 5, 6, 2, 1, 0, 5, 2], [.braid 4, .commute 6, .commute 7])
,
  ([0, 8, 5, 6, 2, 1, 0, 5, 2, 1], [0, 8, 5, 6, 2, 1, 0, 5, 2, 1], [])
,
  ([0, 8, 5, 6, 2, 1, 0, 5, 2, 1, 8], [0, 5, 2, 1, 0, 8, 6, 0, 5, 2, 1], [.commute 9, .commute
    8, .commute 7, .commute 1, .commute 2, .commute 3, .commute 4, .braid 5, .commute 2,
    .commute 3, .commute 4, .commute 5])
,
  ([0, 5, 2, 1, 0, 8, 6, 0, 5, 2, 1, 6], [0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 2, 1], [.commute 10,
    .commute 9, .commute 6, .braid 7])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 2, 1, 2], [0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 1, 2, 1], [.braid
    10])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 1, 2, 1, 0], [0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 1, 2, 1, 0], [])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 5, 1, 2, 1, 0, 5], [0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2, 0],
    [.commute 9, .commute 10, .commute 11, .braid 12, .braid 9, .commute 11, .commute 12])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2, 0, 1], [0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2,
    0, 1], [])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2, 0, 1, 8], [0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6,
    0, 5, 2, 1], [.commute 15, .commute 13, .commute 14, .braid 11, .commute 13, .braid 4,
    .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .braid 11, .commute 7, .commute
    8, .commute 6, .commute 7, .braid 8, .commute 10, .commute 11, .commute 5, .commute 3,
    .commute 2, .braid 3, .braid 5, .commute 7, .braid 8, .commute 10, .commute 6, .commute 7,
    .commute 4, .commute 5, .commute 6, .commute 4, .commute 3, .commute 1])
,
  ([0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 0, 5, 2, 1, 2], [0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5,
    6, 0, 5, 1, 2, 1], [.braid 15])
,
  ([0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 0, 5, 1, 2, 1, 6], [0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8,
    0, 5, 6, 0, 5, 1, 2, 1], [.commute 17, .commute 16, .commute 15, .commute 12, .braid 13,
    .braid 11, .commute 13])
,
  ([0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 0, 5, 1, 2, 1, 0], [0, 8, 5, 6, 1, 0, 5, 2, 1, 0,
    8, 0, 5, 6, 0, 5, 1, 2, 1, 0], [])
,
  ([0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 0, 5, 1, 2, 1, 0, 1], [0, 8, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 0, 5, 6, 0, 5, 1, 2, 0, 1, 0], [.braid 18])
,
  ([0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 0, 5, 1, 2, 0, 1, 0, 8], [0, 5, 2, 8, 1, 0, 8, 5,
    6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 2, 0, 1], [.braid 18, .commute 20, .braid 9, .commute 11,
    .commute 12, .commute 6, .commute 7, .commute 8, .braid 9, .commute 11, .braid 12, .commute
    14, .commute 15, .commute 16, .commute 17, .braid 18, .braid 15, .commute 17, .commute 18,
    .commute 3, .commute 4, .commute 5, .commute 6, .commute 7, .commute 8, .braid 9, .commute
    11, .braid 12, .commute 14, .braid 15, .commute 17, .commute 10, .commute 11, .commute 9,
    .braid 7, .braid 9, .braid 11, .commute 13, .commute 14, .commute 15, .commute 16, .commute
    12, .commute 13, .commute 10, .commute 11, .commute 4, .braid 5, .commute 7, .commute 8,
    .commute 9, .braid 3, .commute 5, .commute 6, .commute 7, .commute 8, .braid 9, .braid 11,
    .braid 13, .commute 15, .commute 12, .commute 10, .commute 11, .commute 1, .commute 2])
,
  ([0, 5, 2, 8, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 2, 0, 1], [0, 5, 2, 1, 0, 8, 0, 5,
    6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 2, 0, 1], [.commute 3, .braid 4])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 2, 0, 1, 5], [0, 5, 2, 1, 0, 8, 0,
    5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1], [.commute 21, .commute 19, .commute 20])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 1, 2], [0, 5, 2, 1, 0, 8,
    0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 1, 2, 1], [.braid 21])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 1, 2, 1, 6], [0, 5, 2, 1, 0,
    8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 1, 2, 1], [.commute 23, .commute 22,
    .commute 21, .commute 17, .commute 18, .braid 19, .commute 16, .braid 17, .commute 19])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 1, 2, 1, 0], [0, 5, 2, 1,
    0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 1, 2, 1, 0], [])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 1, 2, 1, 0, 5], [0, 5, 2,
    1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [.commute 21,
    .commute 22, .commute 23, .braid 24, .braid 21, .commute 23, .commute 24, .commute 20,
    .braid 21, .commute 23])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0, 6], [0, 5,
    2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [.commute 26,
    .commute 25, .commute 24, .commute 19, .commute 20, .commute 21, .braid 22, .commute 18,
    .commute 19, .braid 20, .commute 22, .commute 17, .braid 18, .commute 20, .commute 21,
    .braid 16, .commute 18, .commute 19, .commute 20])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0, 1], [0,
    5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0, 1], [])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0, 1, 1],
    [0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0],
    [.square 28])
,
  ([0, 2, 1, 5, 0, 1, 2, 6, 5, 0, 1, 2, 8, 0, 1, 2, 5, 0, 1, 6, 5, 0, 8, 0, 1, 2, 3, 5, 0], [2,
    5, 0, 1, 2, 6, 5, 0, 8, 0, 1, 2, 5, 0, 6, 5, 1, 0, 8, 6, 1, 0, 5, 0, 1, 2, 3, 1, 0],
    [.commute 15, .commute 16, .commute 14, .commute 2, .braid 3, .commute 5, .commute 6, .braid
    7, .commute 9, .commute 10, .commute 11, .braid 12, .braid 14, .braid 16, .commute 18,
    .commute 19, .commute 20, .commute 21, .commute 22, .braid 23, .commute 25, .commute 26,
    .commute 25, .commute 24, .commute 23, .commute 15, .commute 10, .commute 11, .commute 12,
    .braid 13, .braid 15, .commute 17, .braid 18, .commute 20, .braid 21, .commute 16, .commute
    17, .commute 15, .commute 12, .commute 13, .commute 0, .braid 1, .commute 3, .commute 4,
    .braid 5, .commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .braid
    13, .braid 15, .braid 17, .commute 19, .commute 14, .commute 8, .braid 9, .commute 11,
    .braid 12, .braid 14, .commute 16, .commute 17, .commute 18])
,
  ([2, 5, 0, 1, 2, 6, 5, 0, 8, 0, 1, 2, 5, 0, 6, 5, 1, 0, 8, 6, 1, 0, 5, 0, 1, 2, 3, 1, 0], [5,
    6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 0, 1, 2, 3, 1, 0],
    [.commute 15, .commute 13, .commute 4, .commute 5, .commute 6, .commute 7, .commute 8,
    .braid 9, .commute 11, .commute 12, .braid 13, .braid 15, .commute 17, .commute 14, .commute
    10, .commute 11, .commute 12, .commute 13, .commute 9, .commute 10, .commute 3, .commute 4,
    .commute 0, .commute 1, .commute 2, .commute 3, .commute 1])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 1, 0, 5, 0, 1, 2, 3, 1, 0, 0, 5,
    2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [5, 6, 0, 5,
    2, 1, 0, 8, 2, 1, 0, 5, 6, 5, 2, 1, 0, 5, 8, 0, 1, 2, 1, 3, 0, 1, 2, 1, 0, 8, 5, 6, 1, 0, 5,
    2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [.square 28, .braid 21, .commute 23,
    .commute 24, .commute 25, .commute 26, .square 27, .commute 17, .commute 18, .commute 19,
    .commute 20, .commute 13, .commute 14, .braid 15, .commute 17, .commute 12, .braid 13,
    .commute 15, .commute 16, .braid 17, .commute 10, .commute 11, .commute 12, .commute 13,
    .braid 14, .commute 9, .commute 10, .commute 11, .braid 12, .commute 14, .braid 15, .commute
    17, .braid 18, .braid 20, .commute 22, .commute 23, .commute 24, .commute 25, .commute 26,
    .commute 27, .braid 28, .square 30, .braid 16, .commute 18, .commute 19, .braid 20, .commute
    22, .commute 23, .braid 9, .commute 11, .commute 12, .commute 13, .commute 14, .commute 8,
    .braid 9, .commute 11, .commute 12, .commute 13, .braid 14, .commute 16, .commute 17,
    .commute 18, .commute 19, .braid 20])
,
  ([5, 6, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 5, 2, 1, 0, 5, 8, 0, 1, 2, 1, 3, 0, 1, 2, 1, 0, 8, 5,
    6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 0], [5, 6, 0, 5, 2, 6, 0, 1, 2, 8,
    0, 1, 5, 6, 8, 0, 8, 5, 0, 1, 2, 3, 0, 2, 1, 0, 5, 6, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0,
    5, 1, 2, 0], [.commute 22, .braid 23, .commute 25, .braid 26, .commute 28, .commute 29,
    .commute 30, .square 31, .braid 24, .commute 26, .commute 27, .commute 28, .commute 29,
    .commute 30, .commute 31, .square 32, .braid 11, .commute 13, .commute 14, .commute 15,
    .commute 12, .commute 13, .commute 10, .commute 11, .commute 9, .commute 8, .braid 9, .braid
    11, .braid 13, .braid 15, .commute 17, .commute 18, .commute 19, .commute 20, .commute 21,
    .commute 22, .commute 23, .commute 24, .commute 25, .commute 26, .braid 27, .braid 29,
    .braid 31, .commute 33, .braid 34, .commute 36, .commute 37, .commute 38, .square 39,
    .commute 26, .commute 27, .commute 16, .commute 14, .commute 7, .commute 8, .commute 9,
    .commute 6, .commute 5, .braid 6, .commute 8, .braid 9, .commute 11, .commute 12, .commute
    13])
,
  ([5, 6, 0, 5, 2, 6, 0, 1, 2, 8, 0, 1, 5, 6, 8, 0, 8, 5, 0, 1, 2, 3, 0, 2, 1, 0, 5, 6, 8, 0, 5,
    1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 1, 2, 0], [2, 0, 6, 5, 0, 1, 2, 6, 8, 0, 5, 6, 1, 0, 5, 8,
    0, 1, 2, 3, 5, 2, 1, 0, 8, 5, 0, 1, 6, 5, 0, 8, 2, 1, 0, 5, 6, 5, 1, 2, 0], [.braid 14,
    .braid 16, .commute 18, .commute 19, .commute 20, .commute 11, .commute 12, .commute 3,
    .commute 1, .commute 2, .braid 3, .commute 1, .commute 0, .braid 1, .commute 3, .braid 4,
    .commute 6, .commute 7, .commute 8, .braid 9, .commute 11, .braid 12, .commute 14, .commute
    15, .braid 16, .commute 18, .commute 19, .braid 20, .commute 22, .commute 23, .braid 24,
    .commute 26, .braid 27, .commute 29, .commute 30, .braid 31, .commute 33, .braid 34,
    .commute 36, .commute 37, .square 38, .commute 29, .commute 21, .braid 22, .commute 24,
    .commute 25, .commute 26, .braid 27, .braid 29, .commute 31, .commute 32, .commute 33,
    .braid 34, .commute 36, .square 37, .commute 25, .commute 26, .commute 27, .commute 24,
    .commute 14, .braid 2, .commute 4, .commute 5, .commute 6])
,
  ([2, 0, 6, 5, 0, 1, 2, 6, 8, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 3, 5, 2, 1, 0, 8, 5, 0, 1, 6, 5, 0,
    8, 2, 1, 0, 5, 6, 5, 1, 2, 0], [0, 6, 5, 0, 1, 2, 8, 0, 1, 5, 0, 6, 5, 8, 0, 1, 2, 3, 2, 1,
    0, 8, 5, 6, 0, 5, 0, 1, 0, 8, 2, 1, 0, 5, 6, 2, 0], [.commute 7, .commute 8, .braid 9,
    .commute 11, .braid 12, .braid 14, .commute 16, .commute 17, .commute 18, .commute 19,
    .commute 20, .commute 21, .braid 22, .braid 24, .commute 26, .braid 27, .commute 29,
    .commute 30, .commute 31, .commute 32, .commute 33, .braid 34, .square 36, .commute 23,
    .commute 19, .commute 20, .braid 21, .braid 23, .commute 25, .commute 26, .commute 27,
    .braid 28, .commute 30, .braid 31, .commute 33, .commute 34, .square 35, .commute 25,
    .commute 26, .commute 24, .commute 22, .commute 10, .commute 11, .commute 9, .commute 0,
    .commute 1, .commute 2, .commute 3, .braid 4, .commute 6, .braid 7, .braid 9, .braid 11,
    .commute 13, .commute 14, .commute 15, .commute 16, .commute 17, .commute 18, .commute 19,
    .commute 20, .commute 21, .braid 22, .braid 24])
,
  ([0, 6, 5, 0, 1, 2, 8, 0, 1, 5, 0, 6, 5, 8, 0, 1, 2, 3, 2, 1, 0, 8, 5, 6, 0, 5, 0, 1, 0, 8, 2,
    1, 0, 5, 6, 2, 0], [6, 5, 0, 1, 2, 8, 0, 5, 1, 0, 6, 5, 3, 2, 1, 8, 0, 8, 5, 6, 1, 0, 5, 2,
    1, 0, 8, 3, 2, 1, 0, 5, 6], [.braid 26, .commute 28, .braid 29, .commute 31, .commute 32,
    .commute 33, .square 34, .commute 25, .commute 8, .commute 0, .braid 1, .commute 3, .commute
    4, .commute 5, .braid 6, .braid 8, .commute 10, .commute 11, .commute 12, .braid 13,
    .commute 15, .commute 16, .commute 17, .braid 18, .commute 20, .commute 21, .commute 22,
    .braid 23, .braid 25, .commute 27, .commute 28, .commute 29, .braid 30, .commute 32, .square
    33, .braid 15, .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .commute 22,
    .commute 23, .commute 24, .commute 25, .commute 26, .commute 23, .commute 14, .braid 15,
    .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .commute 22, .commute 13,
    .commute 14, .braid 15, .commute 17, .commute 18, .commute 19, .commute 12, .commute 13,
    .commute 14])
,
  ([6, 5, 0, 1, 2, 8, 0, 5, 1, 0, 6, 5, 3, 2, 1, 8, 0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0,
    5, 6], [6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6], [.braid 15, .commute 9, .commute 8, .commute 4, .commute 5, .commute 6,
    .commute 7, .commute 3])
,
  ([6, 5, 0, 1, 2, 3, 8, 0, 1, 2, 5, 0, 1, 6, 5, 0, 8, 0, 1, 2, 3, 5, 0, 1, 2, 6, 5, 0, 1, 8, 0,
    5, 6], [6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6], [.commute 28, .commute 24, .commute 25, .commute 26, .commute 27, .commute
    20, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25, .commute 26, .commute
    22, .commute 23, .commute 19, .commute 20, .commute 21, .commute 22, .commute 20, .commute
    18, .commute 19, .commute 12, .commute 13, .commute 9, .commute 10, .commute 11, .commute
    12, .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .commute 11,
    .commute 9, .commute 7, .commute 8, .commute 4, .commute 5, .commute 6, .commute 7, .commute
    3])
,
  ([6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0,
    5, 6, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 3, 1, 2, 0], [6, 5, 0, 8, 1,
    0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 1, 2, 1, 0, 5, 6, 5, 0, 1, 8, 0, 5, 2, 0, 3, 1, 2, 8,
    0, 1, 8, 0, 5, 6, 1, 0, 5, 2, 3, 1, 2, 0], [.commute 32, .braid 30, .braid 32, .square 34,
    .commute 33, .commute 34, .commute 31, .commute 32, .commute 29, .commute 30, .commute 28,
    .commute 29, .braid 30, .braid 32, .braid 34, .square 36, .commute 35, .commute 36, .commute
    33, .commute 34, .commute 31, .commute 32, .commute 27, .commute 28, .commute 29, .commute
    30, .commute 31, .braid 32, .braid 34, .braid 36, .square 38, .commute 26, .commute 27,
    .commute 28, .commute 22, .commute 23, .braid 24, .commute 26, .commute 21, .braid 22,
    .commute 24, .commute 25, .braid 26, .braid 28, .commute 30, .commute 31, .commute 32,
    .commute 33, .commute 34, .commute 19, .commute 20, .commute 21, .commute 22, .braid 23,
    .commute 18, .commute 19, .commute 20, .braid 21, .commute 23, .braid 24, .commute 26,
    .commute 27, .braid 28, .commute 30])
,
  ([6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 1, 2, 1, 0, 5, 6, 5, 0, 1, 8, 0, 5, 2,
    0, 3, 1, 2, 8, 0, 1, 8, 0, 5, 6, 1, 0, 5, 2, 3, 1, 2, 0], [6, 5, 0, 8, 1, 2, 3, 5, 0, 1, 2,
    6, 5, 6, 0, 8, 1, 0, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 1, 2, 3, 0, 1, 2, 8, 0, 1, 8, 0, 5, 6,
    1, 0, 5, 2, 3, 1, 2, 0], [.commute 31, .commute 26, .braid 15, .commute 17, .commute 18,
    .commute 19, .commute 14, .braid 15, .commute 17, .commute 13, .commute 14, .braid 15,
    .braid 17, .braid 19, .commute 21, .commute 22, .commute 23, .braid 24, .braid 26, .commute
    28, .commute 16, .braid 14, .braid 16, .commute 18, .commute 19, .commute 20, .commute 21,
    .commute 22, .commute 23, .commute 24, .commute 17, .commute 15, .commute 13, .commute 14,
    .braid 15, .braid 17, .commute 19, .commute 20, .commute 21, .commute 11, .commute 12,
    .commute 13, .commute 10, .commute 9, .braid 10, .commute 12, .braid 13, .commute 15,
    .commute 16, .braid 17, .commute 19, .commute 7, .commute 8, .commute 9, .commute 10,
    .commute 11, .commute 6, .commute 7, .commute 5, .commute 6, .braid 7, .commute 9, .commute
    10, .braid 11])
,
  ([6, 5, 0, 8, 1, 2, 3, 5, 0, 1, 2, 6, 5, 6, 0, 8, 1, 0, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 1, 2,
    3, 0, 1, 2, 8, 0, 1, 8, 0, 5, 6, 1, 0, 5, 2, 3, 1, 2, 0], [6, 5, 0, 8, 1, 2, 3, 5, 0, 1, 2,
    6, 0, 5, 6, 8, 0, 1, 5, 0, 8, 2, 0, 5, 0, 1, 2, 3, 6, 5, 0, 1, 2, 8, 1, 0, 5, 6, 5, 2, 3, 1,
    2, 0], [.commute 13, .commute 14, .commute 15, .commute 16, .braid 17, .braid 19, .braid 21,
    .commute 23, .braid 24, .commute 26, .commute 27, .braid 28, .commute 30, .braid 31,
    .commute 33, .braid 34, .commute 36, .square 37, .braid 35, .commute 37, .commute 38,
    .square 39, .commute 27, .commute 28, .commute 29, .braid 25, .commute 27, .commute 28,
    .braid 29, .commute 31, .commute 32, .commute 33, .commute 34, .braid 35, .commute 37,
    .square 38, .commute 18, .braid 16, .braid 18, .commute 20, .commute 21, .commute 22,
    .commute 23, .commute 24, .commute 25, .commute 26, .commute 27, .commute 19, .commute 17,
    .commute 15, .commute 16, .braid 17, .braid 19, .commute 21, .commute 22, .commute 14,
    .commute 15, .braid 12, .commute 14, .braid 15, .commute 17, .commute 18, .braid 19,
    .commute 21])
,
  ([6, 5, 0, 8, 1, 2, 3, 5, 0, 1, 2, 6, 0, 5, 6, 8, 0, 1, 5, 0, 8, 2, 0, 5, 0, 1, 2, 3, 6, 5, 0,
    1, 2, 8, 1, 0, 5, 6, 5, 2, 3, 1, 2, 0], [6, 5, 0, 8, 1, 2, 3, 5, 0, 1, 2, 6, 0, 5, 8, 0, 1,
    2, 0, 8, 5, 6, 0, 5, 1, 0, 8, 1, 3, 2, 1, 0, 5, 6, 2, 0], [.braid 22, .commute 24, .commute
    25, .commute 26, .braid 27, .commute 29, .commute 30, .commute 31, .commute 32, .commute 33,
    .commute 34, .braid 35, .square 37, .commute 31, .commute 30, .braid 31, .commute 33,
    .commute 34, .commute 35, .square 36, .commute 26, .commute 27, .commute 28, .commute 29,
    .commute 25, .commute 26, .commute 27, .commute 28, .braid 29, .commute 31, .commute 32,
    .commute 33, .commute 34, .square 35, .commute 20, .commute 21, .commute 19, .commute 18,
    .braid 19, .braid 21, .commute 23, .commute 24, .commute 25, .braid 26, .commute 28,
    .commute 29, .braid 30, .commute 32, .commute 33, .square 34, .commute 23, .commute 24,
    .commute 22, .commute 20, .commute 14, .commute 15, .commute 16, .commute 17, .commute 18,
    .commute 19, .braid 20, .braid 22, .braid 24, .commute 26])
,
  ([6, 5, 0, 8, 1, 2, 3, 5, 0, 1, 2, 6, 0, 5, 8, 0, 1, 2, 0, 8, 5, 6, 0, 5, 1, 0, 8, 1, 3, 2, 1,
    0, 5, 6, 2, 0], [6, 5, 0, 1, 2, 3, 5, 6, 1, 0, 8, 5, 0, 2, 1, 0, 5, 6, 8, 2, 0, 5, 1, 0, 8,
    3, 2, 1, 0, 5, 6, 1], [.commute 27, .braid 28, .commute 30, .commute 31, .commute 32,
    .square 33, .commute 23, .commute 10, .commute 11, .commute 12, .commute 13, .commute 14,
    .braid 15, .commute 9, .commute 8, .braid 9, .commute 11, .commute 12, .braid 13, .commute
    15, .braid 16, .commute 18, .commute 19, .commute 20, .braid 21, .braid 23, .commute 25,
    .commute 26, .commute 27, .commute 28, .braid 29, .commute 31, .square 32, .commute 18,
    .commute 19, .commute 11, .commute 3, .commute 4, .commute 5, .commute 6, .commute 7,
    .commute 8, .braid 9, .braid 11, .commute 13, .commute 14, .commute 15, .braid 16, .commute
    18, .braid 19, .commute 21, .commute 22, .braid 23, .commute 25, .commute 26, .braid 27,
    .commute 29, .commute 30, .commute 21, .braid 13, .commute 15, .commute 16, .commute 17,
    .commute 18])
,
  ([6, 5, 0, 1, 2, 3, 5, 6, 1, 0, 8, 5, 0, 2, 1, 0, 5, 6, 8, 2, 0, 5, 1, 0, 8, 3, 2, 1, 0, 5, 6,
    1], [0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0,
    5, 6, 1], [.commute 19, .commute 20, .commute 5, .commute 6, .commute 7, .commute 8,
    .commute 9, .commute 10, .commute 11, .commute 4, .commute 5, .commute 3, .commute 4, .braid
    5, .commute 7, .commute 8, .commute 9, .commute 10, .braid 11, .commute 13, .commute 14,
    .commute 15, .commute 16, .commute 17, .commute 18, .commute 19, .commute 10, .commute 11,
    .braid 12, .commute 14, .commute 15, .commute 16, .braid 1, .commute 3, .commute 4, .braid
    5, .commute 7, .commute 8, .commute 9, .braid 10, .commute 12, .commute 13, .commute 14,
    .commute 15, .commute 14, .commute 13, .commute 7, .commute 8, .commute 9, .commute 10,
    .braid 11, .commute 0, .braid 1, .commute 3, .commute 4, .braid 5, .commute 7, .commute 8,
    .braid 9, .commute 11])
,
  ([0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6,
    1, 6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1,
    0, 5, 6], [0, 5, 6, 2, 1, 0, 5, 3, 0, 8, 1, 2, 0, 1, 3, 2, 0, 3, 5, 0, 8, 5, 3, 2, 1, 0, 8,
    0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [.commute 30, .square 31, .commute 29,
    .square 30, .braid 27, .square 29, .commute 24, .commute 25, .commute 23, .commute 24,
    .braid 25, .commute 27, .square 28, .square 27, .square 26, .commute 19, .commute 20,
    .commute 21, .commute 22, .commute 23, .commute 24, .square 25, .commute 15, .commute 16,
    .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .commute 22, .commute 23,
    .square 24, .commute 22, .square 23, .commute 20, .commute 21, .square 22, .commute 17,
    .commute 18, .commute 19, .commute 11, .braid 9, .braid 11, .commute 13, .commute 14,
    .commute 15, .commute 16, .commute 17, .commute 18, .braid 19, .square 21, .commute 13,
    .commute 14, .commute 15, .commute 16, .commute 17, .commute 12, .commute 10, .commute 8,
    .commute 9, .braid 10, .braid 12, .commute 14, .commute 15])
,
  ([0, 5, 6, 2, 1, 0, 5, 3, 0, 8, 1, 2, 0, 1, 3, 2, 0, 3, 5, 0, 8, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1,
    0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [2, 3, 6, 5, 0, 1, 2, 5, 3, 8, 5, 2, 1, 0, 8, 3, 2, 1,
    0, 5, 6], [.commute 16, .braid 17, .commute 19, .square 20, .commute 16, .commute 17,
    .commute 18, .square 19, .commute 15, .commute 16, .commute 17, .square 18, .commute 13,
    .commute 14, .commute 12, .commute 6, .commute 5, .braid 6, .commute 8, .commute 9, .commute
    10, .commute 11, .braid 12, .braid 14, .commute 16, .square 17, .commute 8, .commute 9,
    .commute 10, .commute 4, .commute 5, .braid 6, .commute 8, .commute 9, .braid 10, .commute
    12, .commute 13, .braid 14, .square 16, .square 15, .square 14, .commute 12, .square 13,
    .commute 2, .commute 3, .commute 1, .commute 2, .braid 3, .commute 5, .commute 6, .commute
    7, .commute 8, .commute 9, .commute 10, .commute 11, .square 12, .square 11, .square 10,
    .commute 0, .commute 1, .commute 2, .braid 3, .commute 5, .commute 6])
,
  ([2, 3, 6, 5, 0, 1, 2, 5, 3, 8, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [6, 5, 1, 0, 8, 0, 5, 6, 1],
    [.commute 7, .commute 8, .square 9, .commute 1, .commute 2, .commute 3, .commute 4, .braid
    5, .commute 7, .square 8, .commute 0, .commute 1, .commute 2, .braid 3, .commute 5, .commute
    6, .square 7, .commute 5, .commute 6, .commute 7, .square 8, .commute 4, .commute 5,
    .commute 6, .square 7, .braid 4, .braid 2, .commute 4, .braid 5, .square 7, .commute 6,
    .commute 7])
,
  ([1, 6, 5, 0, 8, 0, 1, 5, 6], [6, 5, 1, 0, 8, 0, 5, 6, 1], [.commute 6, .commute 7, .commute
    0, .commute 1])
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
