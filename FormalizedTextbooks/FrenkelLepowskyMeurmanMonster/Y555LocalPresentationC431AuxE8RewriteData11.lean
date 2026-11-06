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
def y431AuxE8RewriteData11 : Fin 64 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
![
  ([8, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3,
    2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 2, 3, 4, 3, 3], [8, 5, 6, 2, 1, 0, 5, 3, 2,
    1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0,
    8, 2, 1, 0, 5, 6, 1, 2, 3, 4], [.square 50])
,
  ([8, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3,
    2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 2, 3, 4, 0], [8, 5, 6, 2, 1, 0, 5, 3, 2, 1,
    0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8,
    2, 1, 0, 5, 6, 1, 2, 3, 4, 0], [])
,
  ([8, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3,
    2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 2, 3, 4, 0, 1], [8, 5, 6, 2, 1, 0, 5, 3, 2,
    1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0,
    8, 2, 1, 0, 5, 6, 1, 2, 3, 4, 0, 1], [])
,
  ([8, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3,
    2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 2, 3, 4, 0, 1, 5], [8, 5, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1,
    0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 2, 3, 4, 1], [.commute 51, .commute 49, .commute 50, .commute
    48, .commute 49, .commute 47, .commute 48])
,
  ([8, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3,
    2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 2, 3, 4, 1, 8], [8, 5, 6, 2, 1, 0, 5,
    3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 3, 0, 1, 2, 5, 0, 1, 8, 0, 5, 6, 3, 2, 4, 3, 8, 0, 1, 2, 5, 0,
    8, 1, 0, 5, 6, 0, 1, 8, 0, 5, 8, 2, 3, 4, 1, 8], [.commute 40, .commute 41, .commute 39,
    .braid 37, .braid 39, .braid 41, .commute 43, .commute 44, .commute 45, .commute 34,
    .commute 35, .commute 36, .commute 37, .commute 33, .commute 34, .commute 32, .commute 33,
    .braid 34, .commute 36, .braid 37, .commute 39, .commute 40, .braid 41, .commute 43,
    .commute 39, .commute 24, .commute 25, .commute 23, .braid 21, .braid 23, .braid 25,
    .commute 27, .commute 28, .commute 29, .commute 30, .commute 31, .commute 32, .commute 19,
    .commute 20, .commute 21, .commute 18, .commute 17, .braid 18, .commute 20, .braid 21,
    .commute 23, .commute 24, .braid 25, .commute 27, .commute 28, .commute 29, .commute 30,
    .commute 31, .braid 32, .commute 34, .commute 35, .commute 36, .braid 37, .braid 39,
    .commute 41, .commute 42, .braid 43, .braid 45, .commute 47])
,
  ([8, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 3, 0, 1, 2, 5, 0, 1, 8, 0, 5, 6, 3, 2, 4,
    3, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5, 6, 0, 1, 8, 0, 5, 8, 2, 3, 4, 1, 8], [8, 5, 6, 2, 1, 0, 5,
    3, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 1, 2, 3, 0, 1, 2, 4, 3, 1, 0, 8, 5, 0, 1, 2, 6, 0, 5, 0, 8,
    1, 0, 5, 6, 5, 0, 1, 8, 0, 5, 2, 3, 4, 1], [.commute 48, .commute 49, .commute 50, .commute
    51, .square 52, .commute 27, .commute 28, .commute 29, .commute 30, .commute 31, .commute
    32, .commute 33, .commute 34, .commute 26, .commute 27, .commute 28, .commute 29, .commute
    30, .commute 25, .commute 26, .commute 27, .commute 28, .commute 24, .commute 25, .commute
    26, .commute 27, .braid 28, .braid 30, .commute 32, .commute 33, .braid 34, .commute 36,
    .commute 37, .commute 38, .commute 39, .braid 40, .commute 23, .commute 20, .commute 21,
    .commute 17, .commute 18, .commute 19, .commute 20, .braid 21, .braid 23, .commute 25,
    .commute 26, .commute 20, .commute 21, .commute 18, .commute 16, .commute 17, .braid 18,
    .commute 20, .braid 21, .commute 23, .commute 24, .commute 25, .braid 26, .commute 28,
    .commute 29, .braid 30, .commute 32, .commute 33])
,
  ([8, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 1, 2, 3, 0, 1, 2, 4, 3, 1, 0, 8, 5, 0,
    1, 2, 6, 0, 5, 0, 8, 1, 0, 5, 6, 5, 0, 1, 8, 0, 5, 2, 3, 4, 1], [8, 5, 6, 2, 1, 0, 5, 3, 2,
    1, 0, 8, 1, 5, 0, 6, 5, 1, 2, 3, 0, 4, 2, 1, 0, 8, 5, 6, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6,
    5, 0, 8, 2, 1, 0, 5, 2, 3, 4, 0, 1], [.braid 34, .commute 36, .commute 37, .braid 38,
    .commute 40, .braid 41, .commute 43, .commute 44, .braid 45, .commute 47, .commute 48,
    .commute 49, .commute 43, .commute 32, .commute 33, .commute 34, .commute 35, .commute 31,
    .commute 32, .commute 30, .commute 15, .braid 13, .braid 15, .commute 17, .commute 18,
    .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25,
    .commute 26, .commute 27, .braid 28, .braid 30, .braid 32, .commute 34, .braid 35, .commute
    37, .commute 38, .commute 39, .commute 40, .commute 41, .commute 42, .commute 24, .commute
    25, .commute 26, .commute 27, .commute 28, .commute 29, .commute 30, .commute 31, .commute
    32, .commute 33, .commute 22, .commute 21, .braid 22, .commute 24, .commute 25, .commute 26,
    .commute 27, .commute 28, .commute 29])
,
  ([8, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 5, 0, 6, 5, 1, 2, 3, 0, 4, 2, 1, 0, 8, 5, 6, 0, 5, 2,
    1, 0, 8, 3, 2, 1, 0, 5, 6, 5, 0, 8, 2, 1, 0, 5, 2, 3, 4, 0, 1], [8, 5, 6, 5, 3, 2, 1, 0, 5,
    8, 6, 0, 1, 3, 2, 3, 4, 1, 2, 0, 1, 5, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6,
    5, 0, 8, 2, 1, 0, 5, 2, 3, 4, 0, 1], [.commute 20, .commute 21, .braid 22, .commute 24,
    .commute 25, .commute 26, .commute 11, .commute 12, .braid 9, .commute 6, .commute 7,
    .commute 5, .commute 6, .braid 7, .commute 9, .braid 10, .braid 12, .commute 14, .commute
    15, .commute 16, .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .braid 22,
    .commute 15, .commute 16, .commute 17, .commute 18, .commute 19, .commute 20, .commute 13,
    .braid 8, .commute 10, .commute 11, .commute 12, .braid 13, .commute 15, .commute 16,
    .commute 17, .commute 18, .commute 6, .commute 4, .commute 5, .braid 6, .commute 8, .commute
    9, .commute 10, .commute 11, .commute 12, .braid 13, .commute 15, .commute 16, .commute 4,
    .commute 3, .braid 4, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .commute
    11, .commute 12])
,
  ([8, 5, 6, 5, 3, 2, 1, 0, 5, 8, 6, 0, 1, 3, 2, 3, 4, 1, 2, 0, 1, 5, 0, 8, 0, 5, 6, 1, 0, 5, 2,
    1, 0, 8, 3, 2, 1, 0, 5, 6, 5, 0, 8, 2, 1, 0, 5, 2, 3, 4, 0, 1], [8, 5, 6, 5, 3, 2, 1, 0, 5,
    8, 6, 0, 1, 2, 3, 4, 1, 2, 0, 1, 5, 0, 8, 0, 1, 2, 3, 5, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0,
    5, 6, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1], [.braid 13, .commute 15, .braid 16, .braid 18, .braid
    20, .commute 22, .braid 23, .commute 25, .braid 26, .commute 28, .braid 29, .commute 31,
    .commute 32, .braid 33, .commute 35, .commute 36, .commute 37, .commute 38, .commute 39,
    .commute 40, .commute 41, .braid 37, .commute 39, .commute 40, .commute 36, .braid 37,
    .commute 39, .commute 32, .commute 33, .commute 34, .commute 35, .commute 36, .braid 37,
    .commute 34, .commute 35, .commute 31, .commute 32, .commute 33, .commute 28, .commute 29,
    .commute 30, .commute 31, .commute 25, .commute 26, .commute 27, .commute 28, .commute 29,
    .commute 30, .braid 31, .braid 33, .braid 35, .commute 37, .commute 30, .commute 31,
    .commute 32, .commute 33, .commute 28, .commute 29, .commute 30, .commute 26, .commute 27,
    .commute 24, .commute 25, .commute 26])
,
  ([8, 5, 6, 5, 3, 2, 1, 0, 5, 8, 6, 0, 1, 2, 3, 4, 1, 2, 0, 1, 5, 0, 8, 0, 1, 2, 3, 5, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1], [8, 5, 6, 5, 3, 2, 1, 0, 5,
    8, 6, 2, 3, 1, 2, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3, 2, 1, 0,
    5, 6, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1], [.braid 27, .commute 29, .braid 30, .commute 32, .braid
    33, .commute 35, .commute 36, .commute 26, .commute 27, .commute 28, .commute 29, .commute
    30, .commute 31, .commute 25, .commute 26, .commute 27, .braid 23, .commute 25, .commute 26,
    .braid 27, .commute 29, .commute 30, .braid 31, .commute 33, .commute 34, .commute 35,
    .commute 15, .commute 16, .commute 17, .commute 18, .commute 19, .commute 20, .commute 21,
    .commute 22, .commute 23, .commute 24, .commute 25, .commute 26, .commute 27, .commute 28,
    .commute 29, .commute 14, .braid 12, .braid 14, .commute 16, .commute 17, .commute 18,
    .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .commute 15,
    .commute 13, .commute 11, .commute 12, .braid 13, .braid 15, .commute 17, .commute 18,
    .commute 19, .commute 16, .commute 14])
,
  ([8, 5, 6, 5, 3, 2, 1, 0, 5, 8, 6, 2, 3, 1, 2, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4,
    3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1], [6, 5, 3, 2, 1, 0, 8, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0,
    5, 6, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1], [.commute 8, .braid 1, .commute 3, .commute 4, .commute
    5, .commute 6, .commute 7, .braid 8, .commute 10, .commute 11, .commute 12, .commute 13,
    .braid 14, .braid 16, .commute 18, .braid 19, .commute 21, .commute 22, .commute 23, .braid
    24, .commute 26, .commute 27, .commute 28, .braid 29, .commute 31, .commute 32, .commute 33,
    .commute 34, .commute 13, .commute 14, .commute 11, .commute 12, .commute 13, .commute 0,
    .commute 1, .commute 2, .commute 3, .commute 4, .braid 5])
,
  ([6, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3,
    2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1, 2], [6, 5, 3, 2, 1, 0, 8, 0,
    5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 4, 3, 2, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1, 2], [])
,
  ([6, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3,
    2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1, 2, 6], [6, 5, 3, 2, 1, 0, 8,
    0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0,
    5, 6, 4, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1, 2], [.commute 41, .commute 42, .commute 43, .commute
    44, .commute 40, .commute 41, .commute 42, .commute 39, .commute 40, .commute 38, .braid 36,
    .braid 38, .braid 40, .braid 42, .braid 44, .commute 46, .commute 47, .commute 48, .commute
    49, .commute 50, .commute 51, .square 52, .commute 43, .commute 41, .commute 42, .commute
    39, .commute 40, .commute 41, .commute 37, .commute 38, .commute 39, .commute 40, .commute
    35, .commute 36, .commute 37, .commute 38, .commute 39])
,
  ([6, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3,
    2, 1, 0, 8, 2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1, 2, 3], [6, 5, 3, 2, 1, 0, 8, 0,
    5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5,
    6, 4, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1, 2, 3], [])
,
  ([6, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3,
    2, 1, 0, 8, 2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1, 2, 3, 0], [6, 5, 3, 2, 1, 0, 8,
    0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0,
    5, 6, 4, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1, 2, 3, 0], [])
,
  ([6, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3,
    2, 1, 0, 8, 2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1, 2, 3, 0, 1], [6, 5, 3, 2, 1, 0,
    8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1,
    0, 5, 6, 4, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1, 2, 3, 0, 1], [])
,
  ([6, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3,
    2, 1, 0, 8, 2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 2, 3, 4, 0, 1, 2, 3, 0, 1, 5], [6, 5, 3, 2, 1,
    0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2,
    1, 0, 5, 6, 1, 0, 5, 2, 3, 4, 0, 1, 2, 3, 2, 0, 1, 0], [.commute 45, .commute 46, .commute
    47, .commute 44, .commute 45, .commute 46, .braid 47, .commute 49, .commute 50, .commute 51,
    .braid 42, .commute 44, .commute 45, .commute 46, .braid 47, .commute 49, .commute 50,
    .braid 51, .commute 53, .square 54, .commute 41, .braid 42, .commute 44, .commute 45,
    .commute 46, .braid 47, .commute 49, .commute 50, .braid 51, .commute 40, .commute 41,
    .braid 42, .commute 44, .commute 45, .commute 46, .braid 47, .commute 49, .commute 48,
    .commute 47, .commute 46, .braid 44, .commute 43, .commute 44, .commute 42, .commute 43,
    .commute 41, .commute 42])
,
  ([6, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3,
    2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 2, 3, 4, 0, 1, 2, 3, 2, 0, 1, 0, 8], [6, 5, 3, 2, 1, 0,
    8, 0, 5, 6, 2, 3, 0, 1, 2, 5, 0, 1, 8, 0, 5, 6, 3, 2, 4, 3, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5, 6,
    0, 1, 0, 8, 0, 5, 2, 3, 4, 0, 1, 2, 3, 2, 1, 0, 8, 1], [.braid 51, .commute 53, .commute 34,
    .commute 35, .commute 33, .braid 31, .braid 33, .braid 35, .commute 37, .commute 38,
    .commute 39, .commute 28, .commute 29, .commute 30, .commute 31, .commute 27, .commute 28,
    .commute 26, .commute 27, .braid 28, .commute 30, .braid 31, .commute 33, .commute 34,
    .braid 35, .commute 37, .commute 33, .commute 18, .commute 19, .commute 17, .braid 15,
    .braid 17, .braid 19, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25,
    .commute 26, .commute 13, .commute 14, .commute 15, .commute 12, .commute 11, .braid 12,
    .commute 14, .braid 15, .commute 17, .commute 18, .braid 19, .commute 21, .commute 22,
    .commute 23, .commute 24, .commute 25, .braid 26, .commute 28, .commute 29, .commute 30,
    .braid 31, .braid 33, .commute 35, .commute 36, .braid 37])
,
  ([6, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 3, 0, 1, 2, 5, 0, 1, 8, 0, 5, 6, 3, 2, 4, 3, 8, 0, 1, 2, 5,
    0, 8, 1, 0, 5, 6, 0, 1, 0, 8, 0, 5, 2, 3, 4, 0, 1, 2, 3, 2, 1, 0, 8, 1], [6, 5, 3, 2, 1, 0,
    8, 0, 5, 6, 0, 5, 1, 2, 3, 0, 1, 2, 4, 3, 1, 0, 8, 5, 0, 1, 2, 6, 0, 5, 0, 8, 1, 0, 5, 6, 5,
    0, 1, 8, 0, 5, 2, 3, 4, 8, 0, 1, 2, 3, 2, 1, 0, 8, 1], [.braid 39, .commute 41, .commute 42,
    .commute 43, .commute 44, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25,
    .commute 26, .commute 27, .commute 28, .commute 20, .commute 21, .commute 22, .commute 23,
    .commute 24, .commute 19, .commute 20, .commute 21, .commute 22, .commute 18, .commute 19,
    .commute 20, .commute 21, .braid 22, .braid 24, .commute 26, .commute 27, .braid 28,
    .commute 30, .commute 31, .commute 32, .commute 33, .braid 34, .commute 17, .commute 14,
    .commute 15, .commute 11, .commute 12, .commute 13, .commute 14, .braid 15, .braid 17,
    .commute 19, .commute 20, .commute 14, .commute 15, .commute 12, .commute 10, .commute 11,
    .braid 12, .commute 14, .braid 15, .commute 17, .commute 18, .commute 19, .braid 20,
    .commute 22, .commute 23, .braid 24, .commute 26, .commute 27])
,
  ([6, 5, 3, 2, 1, 0, 8, 0, 5, 6, 0, 5, 1, 2, 3, 0, 1, 2, 4, 3, 1, 0, 8, 5, 0, 1, 2, 6, 0, 5, 0,
    8, 1, 0, 5, 6, 5, 0, 1, 8, 0, 5, 2, 3, 4, 8, 0, 1, 2, 3, 2, 1, 0, 8, 1], [6, 5, 3, 2, 1, 0,
    8, 0, 5, 6, 0, 5, 1, 2, 3, 0, 1, 2, 4, 3, 1, 0, 8, 5, 0, 1, 2, 5, 6, 0, 5, 8, 0, 1, 8, 0, 8,
    5, 0, 6, 5, 4, 3, 2, 1, 0, 8, 3, 4, 0, 1, 2, 3, 0, 1], [.braid 28, .commute 30, .commute 31,
    .braid 32, .commute 34, .braid 35, .commute 37, .commute 38, .braid 39, .commute 41,
    .commute 42, .commute 43, .braid 44, .commute 46, .commute 47, .commute 48, .commute 49,
    .commute 50, .braid 51, .braid 47, .commute 49, .commute 50, .commute 51, .commute 46,
    .braid 47, .commute 49, .commute 50, .commute 45, .commute 46, .braid 47, .commute 49,
    .commute 44, .commute 45, .commute 46, .braid 47, .braid 42, .commute 44, .commute 45,
    .commute 46, .commute 47, .commute 41, .braid 42, .commute 44, .commute 45, .commute 46,
    .braid 33, .commute 35, .commute 36, .commute 37, .commute 38, .commute 32, .braid 33,
    .commute 35, .commute 36, .commute 31, .commute 32, .braid 33, .commute 30, .commute 31,
    .commute 29, .braid 27, .braid 29, .braid 31, .commute 33])
,
  ([6, 5, 3, 2, 1, 0, 8, 0, 5, 6, 0, 5, 1, 2, 3, 0, 1, 2, 4, 3, 1, 0, 8, 5, 0, 1, 2, 5, 6, 0, 5,
    8, 0, 1, 8, 0, 8, 5, 0, 6, 5, 4, 3, 2, 1, 0, 8, 3, 4, 0, 1, 2, 3, 0, 1], [6, 5, 3, 2, 1, 8,
    0, 8, 5, 6, 0, 5, 1, 2, 3, 4, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 8, 3, 2, 1, 0, 8, 5, 6, 4,
    2, 3, 1, 2, 0, 1, 5, 0, 8, 6, 3, 4, 0, 1, 2, 3, 0, 1], [.braid 34, .braid 36, .braid 38,
    .commute 40, .commute 41, .commute 42, .commute 43, .commute 44, .commute 45, .commute 39,
    .commute 40, .commute 41, .commute 42, .commute 37, .commute 38, .commute 39, .commute 40,
    .braid 32, .commute 34, .commute 35, .commute 36, .commute 37, .commute 38, .commute 26,
    .commute 27, .commute 28, .commute 29, .commute 30, .commute 25, .commute 26, .braid 23,
    .commute 25, .braid 26, .commute 28, .commute 29, .braid 30, .commute 32, .commute 33,
    .commute 34, .commute 35, .commute 36, .commute 19, .commute 20, .commute 21, .commute 22,
    .commute 23, .commute 24, .commute 25, .commute 26, .commute 27, .commute 28, .commute 17,
    .commute 16, .braid 17, .commute 19, .commute 20, .commute 21, .commute 22, .commute 23,
    .commute 15, .commute 16, .braid 17, .commute 19, .braid 5])
,
  ([6, 5, 3, 2, 1, 8, 0, 8, 5, 6, 0, 5, 1, 2, 3, 4, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 8, 3, 2,
    1, 0, 8, 5, 6, 4, 2, 3, 1, 2, 0, 1, 5, 0, 8, 6, 3, 4, 0, 1, 2, 3, 0, 1], [3, 2, 1, 8, 0, 5,
    6, 8, 0, 5, 3, 0, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 8, 4, 3, 2, 1, 0, 8, 5, 6, 3, 4,
    2, 3, 1, 2, 0, 1, 5, 0, 8, 6, 3, 4, 0, 1, 2, 3, 0, 1], [.commute 7, .commute 8, .commute 1,
    .commute 2, .commute 3, .commute 4, .braid 5, .commute 7, .braid 8, .commute 10, .commute
    11, .commute 12, .commute 13, .commute 14, .commute 15, .commute 16, .braid 17, .braid 19,
    .commute 21, .commute 22, .braid 23, .commute 25, .commute 26, .commute 27, .braid 28,
    .commute 30, .commute 31, .commute 32, .commute 33, .commute 34, .commute 14, .commute 15,
    .commute 16, .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .commute 22,
    .commute 23, .commute 24, .commute 25, .commute 26, .braid 12, .commute 14, .commute 15,
    .commute 16, .commute 17, .commute 18, .commute 19, .commute 20, .commute 11, .braid 12,
    .commute 14, .commute 15, .commute 0, .commute 1, .commute 2, .commute 3, .commute 4, .braid
    5, .commute 7, .braid 8, .commute 10])
,
  ([3, 2, 1, 8, 0, 5, 6, 8, 0, 5, 3, 0, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 8, 4, 3, 2, 1,
    0, 8, 5, 6, 3, 4, 2, 3, 1, 2, 0, 1, 5, 0, 8, 6, 3, 4, 0, 1, 2, 3, 0, 1], [3, 2, 1, 0, 8, 5,
    0, 6, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1,
    0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 3, 4, 0, 1, 2, 3, 0, 1], [.commute 11, .braid 12, .commute 14,
    .braid 15, .commute 17, .commute 18, .commute 19, .braid 20, .commute 22, .commute 23,
    .commute 24, .commute 25, .braid 26, .commute 28, .commute 29, .commute 30, .commute 31,
    .commute 32, .commute 33, .braid 34, .braid 36, .braid 38, .braid 40, .braid 42, .commute
    44, .commute 41, .commute 39, .commute 40, .commute 37, .commute 38, .commute 39, .commute
    35, .commute 36, .commute 37, .commute 38, .commute 25, .commute 26, .commute 27, .commute
    28, .braid 29, .commute 6, .commute 7, .commute 5, .braid 3, .braid 5, .braid 7, .commute 9,
    .commute 10, .commute 11, .commute 12, .commute 13, .commute 14, .commute 15, .commute 16,
    .braid 17, .commute 19, .commute 20, .commute 21, .braid 22, .commute 24, .commute 25,
    .commute 26, .braid 27, .commute 29])
,
  ([3, 2, 1, 0, 8, 5, 0, 6, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 3, 4, 0, 1, 2, 3, 0, 1], [3, 2, 1, 0, 8, 5,
    6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1,
    0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 3, 4, 0, 1, 2, 3, 0, 1], [.commute 6])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 3, 4, 0, 1, 2, 3, 0, 1, 2], [3, 2, 1, 0, 8,
    5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2,
    1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 3, 4, 0, 1, 2, 3, 0, 1, 2], [])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 3, 4, 0, 1, 2, 3, 0, 1, 2, 6], [3, 2, 1, 0,
    8, 5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3,
    2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 3, 4, 0, 1, 2, 3, 0, 1, 2], [.commute 46, .commute 47,
    .commute 48, .commute 49, .commute 50, .commute 51, .commute 52, .commute 53, .commute 54,
    .square 55])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 3, 4, 0, 1, 2, 3, 0, 1, 2, 3], [3, 2, 1, 0, 8,
    5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2,
    1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 3, 4, 1, 2, 3, 0, 1, 2], [.commute 51, .commute 52, .commute
    50, .braid 48, .braid 50, .braid 52, .square 54, .commute 51, .commute 49, .commute 50])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 3, 4, 1, 2, 3, 0, 1, 2, 0], [3, 2, 1, 0, 8, 5,
    6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1,
    0, 5, 4, 3, 2, 1, 0, 8, 5, 3, 4, 1, 2, 3, 0, 1, 2, 0], [])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1], [3, 2, 1, 0, 8,
    5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2,
    1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1], [])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1, 5], [3, 2, 1, 0,
    8, 5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3,
    2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 4, 2, 3, 0, 1, 2, 1], [.commute 55, .commute
    53, .commute 54, .braid 51, .commute 53, .commute 45, .commute 46, .commute 47, .commute 48,
    .commute 49, .commute 50, .braid 51, .commute 49, .commute 50, .commute 51, .braid 47,
    .commute 49, .commute 50, .commute 46, .commute 47, .commute 48, .commute 49])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 4, 2, 3, 0, 1, 2, 1, 8], [3, 2, 1,
    0, 8, 5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 4, 3, 2, 5, 0, 1, 8, 0, 5, 6, 3, 4,
    0, 1, 2, 3, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5, 4, 2, 3, 8, 0, 1, 2, 1], [.commute 44, .commute
    45, .commute 46, .commute 43, .commute 44, .commute 42, .braid 40, .braid 42, .braid 44,
    .braid 46, .commute 48, .commute 49, .commute 50, .commute 51, .commute 38, .commute 39,
    .commute 40, .commute 41, .commute 42, .commute 37, .commute 38, .commute 39, .commute 36,
    .commute 35, .braid 36, .commute 38, .braid 39, .commute 41, .braid 42, .commute 44,
    .commute 45, .braid 46, .commute 48, .commute 49, .commute 50, .braid 51, .commute 53,
    .commute 54, .commute 55, .square 56, .commute 44, .commute 29, .braid 27, .braid 29,
    .commute 31, .commute 32, .commute 33, .commute 34, .commute 35, .commute 36, .commute 37,
    .commute 23, .commute 24, .commute 25, .commute 22, .commute 23, .commute 24, .braid 25,
    .commute 27, .commute 28, .braid 29, .commute 31, .commute 32, .commute 33])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 4, 3, 2, 5, 0, 1, 8, 0, 5,
    6, 3, 4, 0, 1, 2, 3, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5, 4, 2, 3, 8, 0, 1, 2, 1], [3, 2, 1, 0, 8,
    5, 6, 0, 5, 1, 3, 0, 8, 2, 3, 1, 2, 0, 1, 4, 3, 2, 6, 5, 0, 8, 1, 0, 5, 6, 3, 4, 5, 0, 1, 2,
    3, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 4, 1, 2, 3, 8, 0, 1, 2, 1], [.commute 27, .commute 13,
    .commute 14, .commute 12, .braid 10, .braid 12, .braid 14, .commute 16, .commute 17,
    .commute 18, .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute 24,
    .braid 25, .braid 27, .commute 29, .commute 30, .commute 31, .commute 32, .braid 33,
    .commute 35, .commute 36, .braid 37, .commute 39, .commute 40, .commute 41, .braid 42,
    .braid 44, .commute 46, .commute 47, .commute 40, .commute 41, .commute 42, .commute 39,
    .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .commute 22, .commute 16,
    .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .braid 22, .commute 24,
    .commute 25, .commute 26, .commute 27, .braid 28, .commute 30, .commute 31, .commute 15,
    .commute 16, .commute 13, .commute 14, .commute 11, .commute 12, .commute 9])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 3, 0, 8, 2, 3, 1, 2, 0, 1, 4, 3, 2, 6, 5, 0, 8, 1, 0, 5, 6, 3,
    4, 5, 0, 1, 2, 3, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 4, 1, 2, 3, 8, 0, 1, 2, 1], [3, 2, 1, 0, 8,
    5, 6, 0, 5, 1, 0, 8, 2, 3, 1, 2, 0, 1, 4, 3, 2, 6, 5, 0, 8, 1, 0, 5, 6, 5, 3, 0, 1, 8, 0, 5,
    4, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 4, 1, 2, 3, 0, 1, 2, 0, 1], [.commute 10, .commute 11,
    .braid 12, .braid 14, .braid 16, .commute 18, .commute 19, .commute 20, .commute 21, .braid
    22, .commute 24, .commute 25, .braid 26, .commute 28, .commute 29, .commute 30, .braid 31,
    .commute 33, .commute 34, .commute 35, .commute 36, .braid 37, .braid 39, .commute 41,
    .braid 42, .commute 44, .commute 45, .commute 46, .braid 47, .commute 49, .commute 50,
    .braid 51, .commute 53, .commute 49, .commute 48, .commute 47, .commute 46, .commute 45,
    .commute 41, .commute 42, .braid 43, .commute 40, .braid 41, .commute 43, .braid 39,
    .commute 41, .commute 42, .commute 35, .commute 36, .commute 37, .commute 34, .commute 35,
    .commute 36, .braid 37, .commute 39, .commute 40, .commute 41, .commute 30, .commute 31,
    .commute 32, .commute 33, .commute 34, .commute 35, .commute 29])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 3, 1, 2, 0, 1, 4, 3, 2, 6, 5, 0, 8, 1, 0, 5, 6, 5, 3,
    0, 1, 8, 0, 5, 4, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 4, 1, 2, 3, 0, 1, 2, 0, 1], [3, 2, 1, 0, 8,
    5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 3, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 4, 3,
    2, 1, 0, 8, 6, 4, 3, 2, 1, 0, 5, 4, 1, 2, 3, 0, 1, 2, 0, 1], [.commute 30, .commute 31,
    .commute 32, .commute 33, .commute 34, .braid 35, .commute 37, .commute 38, .commute 39,
    .commute 40, .braid 27, .commute 29, .commute 30, .commute 31, .commute 32, .commute 26,
    .braid 27, .commute 29, .commute 30, .commute 25, .commute 26, .braid 27, .commute 24,
    .commute 25, .commute 23, .braid 21, .braid 23, .braid 25, .commute 27, .braid 28, .braid
    30, .braid 32, .commute 34, .commute 35, .commute 36, .commute 37, .commute 38, .commute 39,
    .commute 31, .braid 26, .commute 28, .commute 29, .commute 30, .commute 25, .braid 26,
    .commute 20, .commute 21, .commute 22, .commute 23, .commute 19, .commute 20, .commute 21,
    .commute 22, .commute 18, .commute 19, .commute 20, .commute 21, .commute 17, .commute 18,
    .commute 15, .commute 16, .commute 17, .commute 13, .commute 14])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 3, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 4, 3, 2, 1, 0, 5, 4, 1, 2, 3, 0, 1, 2, 0, 1], [3, 2, 1, 0, 8,
    5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 4, 3,
    2, 1, 0, 8, 6, 4, 3, 2, 1, 0, 5, 4, 1, 2, 3, 0, 1, 2, 0, 1], [.commute 15, .commute 16])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 4, 3, 2, 1, 0, 5, 4, 1, 2, 3, 0, 1, 2, 0, 1, 2], [3, 2, 1, 0,
    8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 4,
    3, 2, 1, 0, 8, 6, 4, 3, 2, 1, 0, 5, 4, 1, 2, 3, 1, 2, 0, 1], [.commute 53, .braid 51, .braid
    53, .square 55, .commute 52])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 4, 3, 2, 1, 0, 5, 4, 1, 2, 3, 1, 2, 0, 1, 6], [3, 2, 1, 0, 8,
    5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 4, 3,
    2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 5, 4, 1, 2, 3, 1, 2, 0, 1], [.commute 54, .commute 53,
    .commute 52, .commute 51, .commute 50, .commute 49, .commute 48, .commute 47, .commute 40,
    .commute 41, .commute 42, .commute 43, .commute 44, .braid 45])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 4, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 5, 4, 1, 2, 3, 1, 2, 0, 1, 3], [3, 2, 1, 0,
    8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 4,
    3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 5, 4, 2, 3, 1, 2, 0, 1], [.commute 51, .braid 49, .braid
    51, .commute 53, .commute 54, .square 55, .commute 50])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 4, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 5, 4, 2, 3, 1, 2, 0, 1, 0], [3, 2, 1, 0, 8,
    5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 4, 3,
    2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 5, 4, 2, 3, 1, 2, 0, 1, 0], [])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 4, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 5, 4, 2, 3, 1, 2, 0, 1, 0, 1], [3, 2, 1, 0,
    8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 4,
    3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 5, 4, 2, 3, 1, 2, 1, 0], [.braid 53, .square 55])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 4, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 5, 4, 2, 3, 1, 2, 1, 0, 5], [3, 2, 1, 0, 8,
    5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 4, 3,
    2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 3, 2, 0], [.commute 47, .commute 48,
    .commute 49, .commute 50, .commute 51, .commute 52, .braid 53, .braid 50, .commute 52,
    .commute 53, .braid 48, .commute 50, .commute 51, .commute 52])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 4, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 3, 2, 0, 8], [3, 2, 1, 0,
    8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3,
    2, 1, 0, 3, 8, 4, 2, 3, 1, 2, 0, 1, 6, 5, 0, 8, 5, 6, 0, 5, 3, 2], [.commute 54, .commute
    55, .commute 53, .commute 54, .braid 51, .commute 53, .commute 39, .commute 40, .commute 41,
    .commute 42, .commute 38, .commute 39, .commute 40, .commute 37, .commute 38, .commute 36,
    .braid 34, .braid 36, .braid 38, .braid 40, .braid 42, .commute 44, .commute 45, .commute
    46, .commute 47, .commute 48, .commute 49, .commute 50, .braid 51, .commute 45, .commute 46,
    .commute 47, .commute 48, .commute 44, .commute 45, .commute 46, .commute 47, .braid 48,
    .commute 50, .commute 51, .commute 43, .commute 44, .commute 45, .commute 41, .commute 42,
    .commute 43, .commute 39, .commute 40, .commute 41, .commute 37, .commute 38, .commute 39,
    .commute 35, .commute 36, .commute 37, .commute 38, .braid 39, .braid 41, .braid 43, .braid
    45, .commute 47, .braid 48, .commute 50, .commute 38])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 3, 2, 1, 0, 3, 8, 4, 2, 3, 1, 2, 0, 1, 6, 5, 0, 8, 5, 6, 0, 5, 3, 2], [3, 2, 1, 0,
    8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2,
    1, 0, 8, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 0, 5, 3, 2], [.commute 39, .commute
    40, .commute 41, .commute 42, .commute 43, .commute 37, .commute 38, .commute 39, .commute
    40, .commute 36, .commute 37, .braid 34, .commute 36, .braid 37, .commute 39, .braid 40,
    .commute 42, .braid 43, .commute 45, .commute 46, .commute 47, .braid 48, .commute 45,
    .commute 46, .commute 42, .commute 43, .commute 44, .commute 45, .commute 39, .commute 40,
    .commute 41, .commute 42, .commute 43, .commute 44, .commute 36, .commute 37, .commute 38,
    .commute 39, .commute 40, .commute 41, .commute 42, .commute 43, .commute 41, .commute 39,
    .commute 40, .commute 37, .commute 38, .commute 39, .commute 35, .commute 36, .commute 37,
    .commute 38])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 0, 5, 3, 2, 2], [3, 2, 1,
    0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5,
    2, 1, 0, 8, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 0, 5, 3], [.square 56])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 0, 5, 3, 6], [3, 2, 1, 0,
    8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2,
    1, 0, 8, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 0, 5, 3], [.commute 52, .braid 50, .braid
    52, .commute 54, .square 55, .commute 51])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 0, 5, 3, 3], [3, 2, 1, 0, 8,
    5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 0, 5], [.square 54])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 0, 5, 0], [3, 2, 1, 0, 8, 5,
    6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0,
    8, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 0, 5, 0], [])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 0, 5, 0, 1], [3, 2, 1, 0, 8,
    5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 0, 5, 0, 1], [])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 0, 5, 0, 1, 5], [3, 2, 1, 0,
    8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2,
    1, 0, 8, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 5, 0, 1], [.braid 52, .commute 54,
    .square 55])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 5, 0, 1, 8], [3, 2, 1, 0, 8,
    5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 5, 0, 1], [.commute 49, .commute 50, .commute
    51, .commute 43, .commute 44, .commute 45, .commute 46, .braid 47, .commute 49, .commute 38,
    .commute 39, .commute 40, .commute 41, .commute 42, .commute 43, .commute 44, .commute 45,
    .commute 46, .braid 47, .braid 49, .braid 51, .commute 53, .square 54, .commute 50, .commute
    48, .commute 49, .braid 46, .commute 48, .commute 45, .commute 44, .commute 43, .commute
    42])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 5, 0, 1, 2], [3, 2, 1, 0, 8, 5,
    6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0,
    8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 5, 0, 1, 2], [])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 5, 6, 5, 0, 1, 2, 6], [3, 2, 1, 0, 8,
    5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 5, 0, 1, 2], [.braid 49, .commute 51, .commute 52,
    .commute 53, .square 54])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 5, 0, 1, 2, 3], [3, 2, 1, 0, 8, 5,
    6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0,
    8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 5, 0, 1, 2, 3], [])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 5, 0, 1, 2, 3, 4], [3, 2, 1, 0, 8,
    5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 5, 0, 1, 2, 3, 4], [])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 5, 0, 1, 2, 3, 4, 0], [3, 2, 1, 0,
    8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2,
    1, 0, 8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 5, 0, 1, 2, 3, 4, 0], [])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 5, 0, 1, 2, 3, 4, 0, 1], [3, 2, 1,
    0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5,
    2, 1, 0, 8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 5, 0, 1, 2, 3, 4, 0, 1], [])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 5, 0, 1, 2, 3, 4, 0, 1, 5], [3, 2,
    1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0,
    5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1], [.commute 57,
    .commute 55, .commute 56, .commute 54, .commute 55, .commute 53, .commute 54, .braid 51,
    .commute 53, .commute 50, .braid 51])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 8], [3,
    2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1,
    0, 5, 2, 1, 0, 8, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 0, 5, 0, 1, 2, 3, 4, 1],
    [.commute 58, .commute 57, .commute 56, .commute 55, .commute 54, .commute 48, .commute 49,
    .commute 47, .commute 46, .braid 47, .braid 49, .commute 51, .braid 52, .braid 50, .commute
    52, .commute 49, .braid 50, .commute 46, .commute 47, .commute 42, .commute 43, .commute 44,
    .commute 41, .commute 42, .commute 43, .braid 44, .commute 46, .braid 47, .commute 49,
    .commute 50, .commute 46, .commute 47, .commute 43, .commute 44, .commute 45, .commute 46,
    .commute 42, .commute 43, .commute 44, .commute 45, .commute 41, .commute 42, .commute 43,
    .commute 44, .commute 42, .commute 40, .commute 41, .commute 39, .commute 40, .commute 38,
    .commute 39])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 0, 5, 0, 1, 2, 3, 4, 1, 2],
    [3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5,
    6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 0, 5, 0, 1, 2, 3, 4, 1,
    2], [])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 6, 0, 5, 0, 1, 2, 3, 4, 1, 2,
    6], [3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0,
    5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 5, 0, 1, 2, 3, 4,
    1, 2], [.commute 60, .commute 59, .commute 58, .commute 57, .commute 56, .commute 55,
    .commute 54, .commute 51, .braid 52])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 5, 0, 1, 2, 3, 4, 1, 2,
    3], [3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0,
    5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 5, 0, 1, 2, 3, 4,
    1, 2, 3], [])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 5, 0, 1, 2, 3, 4, 1, 2,
    3, 0], [3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8,
    0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 5, 0, 1, 2, 3,
    4, 1, 2, 3, 0], [])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 5, 0, 1, 2, 3, 4, 1, 2,
    3, 0, 1], [3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0,
    8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 5, 0, 1, 2,
    3, 4, 1, 2, 3, 0, 1], [])
,
  ([3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 5, 0, 1, 2, 3, 4, 1, 2,
    3, 0, 1, 5], [3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1,
    0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0,
    5, 0, 1, 2, 3, 4, 2, 3, 1], [.commute 64, .commute 62, .commute 63, .commute 61, .commute
    62, .commute 59, .commute 60, .commute 61, .commute 58, .commute 59, .commute 60, .braid 56,
    .commute 58, .commute 59, .commute 55, .braid 56, .commute 58, .commute 54, .commute 55,
    .braid 56])
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
