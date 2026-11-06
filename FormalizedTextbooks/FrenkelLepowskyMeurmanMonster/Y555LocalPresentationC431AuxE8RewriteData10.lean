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
/-- Exact bounded chunks of literal E8 square, commutation and braid moves, block 10. -/
def y431AuxE8RewriteData10 : Fin 64 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
![
  ([8, 0, 5, 1, 0, 6, 2, 3, 5, 0, 1, 2, 8, 0, 8, 1, 5, 6, 0, 8, 5, 0, 1, 2, 3, 2, 1, 0, 5, 6, 8,
    0, 5, 1, 2, 0, 8, 1, 0, 5, 6, 5, 0, 8, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 8, 0, 1, 2, 1, 8, 0,
    8], [8, 0, 1, 2, 3, 6, 5, 6, 0, 1, 2, 8, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 3, 2, 1, 0, 8, 5, 0,
    1, 2, 6, 5, 0, 8, 1, 0, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 8, 0, 1, 2, 1, 8,
    0, 8], [.commute 14, .commute 15, .commute 16, .braid 17, .braid 19, .commute 21, .commute
    22, .commute 23, .commute 24, .commute 25, .braid 26, .commute 28, .braid 29, .commute 31,
    .commute 32, .commute 33, .braid 34, .braid 36, .commute 38, .commute 39, .commute 40,
    .commute 31, .commute 32, .commute 14, .commute 15, .commute 4, .commute 5, .commute 6,
    .braid 7, .commute 9, .commute 10, .commute 11, .braid 12, .commute 14, .braid 15, .commute
    17, .commute 18, .braid 19, .commute 21, .commute 22, .commute 23, .braid 24, .commute 26,
    .commute 27, .commute 28, .braid 29, .commute 31, .braid 32, .commute 34, .commute 35,
    .braid 36, .commute 38, .commute 27, .commute 28, .commute 29, .commute 30, .commute 26,
    .commute 17, .commute 4, .commute 5, .commute 2, .commute 3, .commute 4, .braid 5])
,
  ([8, 0, 1, 2, 3, 6, 5, 6, 0, 1, 2, 8, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 3, 2, 1, 0, 8, 5, 0, 1, 2,
    6, 5, 0, 8, 1, 0, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 8, 0, 1, 2, 1, 8, 0,
    8], [8, 0, 1, 2, 3, 6, 5, 0, 1, 2, 8, 0, 5, 6, 1, 3, 0, 2, 1, 5, 0, 8, 0, 5, 1, 0, 2, 1, 3,
    2, 6, 5, 0, 8, 1, 0, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 8, 0, 1, 2, 0, 1, 8,
    0, 8], [.commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .braid 12, .commute
    14, .braid 15, .braid 17, .commute 19, .commute 20, .commute 21, .commute 22, .commute 23,
    .braid 24, .braid 26, .commute 28, .commute 29, .braid 30, .commute 32, .commute 33,
    .commute 34, .commute 35, .braid 36, .braid 38, .braid 40, .commute 42, .braid 43, .commute
    45, .commute 46, .commute 47, .commute 48, .braid 49, .commute 51, .commute 52, .commute 53,
    .braid 54, .commute 56, .braid 20, .commute 22, .commute 23, .commute 24, .commute 25,
    .commute 26, .commute 27, .commute 19, .braid 20, .commute 22, .commute 23, .commute 24,
    .commute 25, .commute 18, .commute 19, .braid 20, .commute 22, .commute 23, .commute 17,
    .commute 18, .commute 19, .braid 20, .commute 16, .commute 17, .commute 18, .commute 15])
,
  ([8, 0, 1, 2, 3, 6, 5, 0, 1, 2, 8, 0, 5, 6, 1, 3, 0, 2, 1, 5, 0, 8, 0, 5, 1, 0, 2, 1, 3, 2, 6,
    5, 0, 8, 1, 0, 5, 6, 0, 5, 1, 0, 8, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 8, 0, 1, 2, 0, 1, 8, 0,
    8], [8, 0, 1, 6, 5, 2, 0, 8, 1, 2, 3, 0, 1, 2, 5, 0, 1, 6, 5, 0, 8, 0, 1, 2, 3, 5, 6, 0, 5,
    1, 0, 8, 2, 1, 0, 5, 6, 0, 5, 1, 0, 8, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 8, 0, 1, 2, 0, 1, 8,
    0, 8], [.commute 16, .commute 14, .commute 9, .commute 10, .commute 11, .commute 12,
    .commute 4, .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10,
    .commute 11, .braid 12, .braid 14, .braid 16, .braid 18, .commute 20, .braid 21, .braid 23,
    .braid 25, .braid 27, .commute 29, .commute 30, .commute 31, .commute 32, .commute 33,
    .commute 34, .commute 35, .commute 36, .commute 37, .commute 38, .commute 39, .commute 40,
    .commute 41, .commute 28, .commute 29, .commute 30, .commute 31, .commute 26, .commute 27,
    .commute 28, .commute 24, .commute 25, .commute 26, .commute 22, .commute 23, .commute 24,
    .commute 11, .commute 12, .commute 13, .commute 14, .commute 15, .commute 16, .commute 10,
    .commute 11, .commute 12, .commute 13, .commute 9, .commute 10, .commute 7, .commute 3,
    .commute 4])
,
  ([8, 0, 1, 6, 5, 2, 0, 8, 1, 2, 3, 0, 1, 2, 5, 0, 1, 6, 5, 0, 8, 0, 1, 2, 3, 5, 6, 0, 5, 1, 0,
    8, 2, 1, 0, 5, 6, 0, 5, 1, 0, 8, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 8, 0, 1, 2, 0, 1, 8, 0,
    8], [8, 0, 6, 5, 0, 1, 2, 3, 8, 0, 1, 2, 5, 6, 0, 8, 5, 0, 1, 2, 3, 0, 5, 6, 8, 0, 5, 1, 0,
    8, 2, 0, 1, 0, 5, 6, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 8, 0, 1, 2, 0, 1, 8,
    0, 8], [.commute 5, .commute 6, .braid 7, .commute 9, .braid 10, .commute 12, .braid 13,
    .commute 15, .braid 16, .commute 18, .commute 19, .commute 20, .commute 21, .commute 22,
    .commute 23, .braid 24, .braid 26, .braid 28, .commute 30, .braid 31, .commute 33, .commute
    34, .commute 35, .commute 36, .commute 37, .braid 18, .commute 20, .commute 21, .commute 22,
    .commute 23, .commute 24, .commute 15, .commute 16, .commute 17, .braid 18, .commute 20,
    .commute 21, .commute 16, .commute 14, .commute 6, .commute 7, .commute 8, .commute 2,
    .commute 3, .braid 4, .commute 6, .commute 7, .braid 8, .commute 10, .commute 11, .commute
    12, .commute 13, .braid 14, .braid 16, .commute 18, .commute 19, .commute 20, .braid 21,
    .commute 23, .braid 24, .commute 26, .commute 27, .braid 28, .commute 30])
,
  ([8, 0, 6, 5, 0, 1, 2, 3, 8, 0, 1, 2, 5, 6, 0, 8, 5, 0, 1, 2, 3, 0, 5, 6, 8, 0, 5, 1, 0, 8, 2,
    0, 1, 0, 5, 6, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 8, 0, 1, 2, 0, 1, 8, 0,
    8], [8, 6, 5, 0, 1, 2, 3, 8, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 3, 1, 0, 5, 6, 8, 0, 1, 5, 0, 8,
    2, 1, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 8, 1, 0, 8, 1, 2, 1,
    0], [.braid 31, .commute 33, .commute 34, .commute 26, .commute 11, .commute 12, .commute
    13, .commute 14, .commute 15, .commute 16, .braid 17, .commute 19, .commute 10, .commute 11,
    .commute 1, .braid 2, .commute 4, .commute 5, .commute 6, .commute 7, .braid 8, .commute 10,
    .braid 11, .commute 13, .commute 14, .braid 15, .commute 17, .commute 18, .braid 19,
    .commute 21, .commute 22, .commute 23, .braid 24, .braid 26, .commute 28, .commute 29,
    .commute 30, .braid 31, .commute 33, .braid 34, .commute 36, .braid 37, .commute 39,
    .commute 40, .braid 41, .commute 43, .commute 44, .commute 45, .commute 46, .commute 47,
    .commute 48, .braid 49, .commute 51, .commute 52, .commute 53, .braid 54, .braid 56, .braid
    58, .square 60, .commute 57, .commute 55, .commute 56, .braid 53, .commute 55])
,
  ([8, 6, 5, 0, 1, 2, 3, 8, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 3, 1, 0, 5, 6, 8, 0, 1, 5, 0, 8, 2, 1,
    0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 8, 1, 0, 8, 1, 2, 1, 0], [8,
    6, 5, 0, 1, 2, 8, 0, 5, 6, 1, 0, 8, 5, 0, 3, 1, 2, 3, 1, 0, 5, 6, 8, 0, 5, 1, 2, 0, 1, 8, 0,
    5, 6, 1, 2, 3, 5, 0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0],
    [.commute 52, .braid 53, .commute 51, .commute 52, .commute 53, .commute 50, .commute 51,
    .commute 52, .braid 48, .commute 50, .commute 51, .commute 47, .braid 48, .commute 50,
    .commute 46, .commute 47, .braid 48, .commute 45, .commute 46, .commute 44, .braid 42,
    .braid 44, .braid 46, .commute 48, .commute 40, .commute 41, .commute 42, .commute 39,
    .commute 38, .braid 39, .commute 41, .braid 42, .commute 44, .commute 45, .braid 46,
    .commute 44, .commute 36, .commute 37, .commute 35, .commute 36, .braid 37, .commute 39,
    .commute 40, .commute 41, .braid 42, .braid 44, .commute 46, .commute 40, .commute 41,
    .commute 42, .commute 39, .commute 28, .commute 29, .commute 27, .commute 25, .commute 6,
    .commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13,
    .commute 14])
,
  ([8, 6, 5, 0, 1, 2, 8, 0, 5, 6, 1, 0, 8, 5, 0, 3, 1, 2, 3, 1, 0, 5, 6, 8, 0, 5, 1, 2, 0, 1, 8,
    0, 5, 6, 1, 2, 3, 5, 0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0], [6,
    5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 8, 5, 0, 1, 2, 3, 2, 1, 0, 5, 6, 8, 0, 5, 1, 2, 8, 0, 1, 2, 8,
    3, 6, 5, 0, 8, 1, 5, 0, 6, 5, 2, 1, 0, 8, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0],
    [.commute 15, .braid 16, .commute 5, .commute 6, .commute 7, .commute 8, .commute 4,
    .commute 0, .commute 1, .braid 2, .braid 4, .commute 6, .commute 7, .braid 8, .commute 10,
    .commute 11, .commute 12, .commute 13, .braid 14, .commute 16, .braid 17, .commute 19,
    .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .braid 25, .braid 27,
    .braid 29, .commute 31, .commute 32, .commute 33, .commute 34, .commute 35, .commute 36,
    .braid 37, .braid 39, .commute 41, .braid 42, .commute 44, .commute 45, .commute 32,
    .commute 33, .commute 34, .commute 31, .commute 32, .commute 33, .braid 34, .commute 36,
    .commute 37, .commute 38, .commute 39, .commute 28, .braid 29, .commute 31, .commute 32,
    .commute 33, .braid 34, .commute 36, .commute 37, .braid 27, .commute 29, .commute 30])
,
  ([6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 8, 5, 0, 1, 2, 3, 2, 1, 0, 5, 6, 8, 0, 5, 1, 2, 8, 0, 1, 2,
    8, 3, 6, 5, 0, 8, 1, 5, 0, 6, 5, 2, 1, 0, 8, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0], [6,
    5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 8, 5, 0, 3, 2, 1, 5, 2, 0, 8, 6, 5, 0, 1, 2, 3, 5, 6, 0, 5, 2,
    1, 0, 8, 0, 5, 6, 1, 2, 0, 1, 5, 0, 8, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0],
    [.commute 31, .commute 32, .commute 33, .braid 34, .commute 26, .commute 27, .braid 28,
    .commute 30, .commute 31, .commute 32, .commute 25, .braid 26, .commute 28, .commute 29,
    .commute 30, .commute 24, .braid 22, .braid 24, .commute 26, .commute 27, .commute 28,
    .commute 21, .commute 22, .braid 19, .commute 21, .braid 22, .commute 24, .commute 25,
    .commute 26, .commute 27, .braid 28, .braid 30, .braid 32, .commute 34, .braid 35, .braid
    37, .braid 39, .commute 41, .commute 42, .commute 43, .commute 44, .commute 40, .commute 41,
    .commute 38, .commute 39, .commute 36, .commute 37, .braid 15, .commute 17, .commute 18,
    .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .braid 25,
    .commute 27, .commute 28, .commute 29, .commute 30, .commute 14, .braid 15, .commute 17])
,
  ([6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 8, 5, 0, 3, 2, 1, 5, 2, 0, 8, 6, 5, 0, 1, 2, 3, 5, 6, 0, 5,
    2, 1, 0, 8, 0, 5, 6, 1, 2, 0, 1, 5, 0, 8, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0], [6,
    5, 0, 8, 1, 0, 5, 6, 2, 1, 3, 2, 8, 0, 5, 1, 6, 0, 5, 8, 0, 1, 2, 3, 0, 5, 6, 1, 2, 0, 8, 1,
    0, 5, 6, 0, 1, 2, 8, 0, 1, 5, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0],
    [.commute 18, .commute 19, .commute 20, .commute 21, .commute 22, .braid 23, .commute 25,
    .commute 26, .commute 27, .commute 16, .commute 13, .commute 14, .commute 12, .commute 13,
    .braid 14, .braid 16, .commute 18, .commute 19, .commute 20, .braid 21, .commute 23,
    .commute 24, .commute 11, .commute 12, .commute 10, .commute 11, .braid 12, .commute 14,
    .commute 15, .braid 16, .commute 18, .braid 19, .commute 21, .commute 22, .commute 23,
    .braid 24, .commute 26, .braid 27, .commute 29, .braid 30, .commute 32, .commute 33,
    .commute 34, .commute 35, .commute 36, .braid 37, .braid 39, .braid 41, .commute 43, .braid
    32, .commute 34, .commute 35, .commute 36, .commute 37, .commute 29, .commute 30, .commute
    31, .braid 32, .commute 34, .commute 30, .commute 28, .commute 17, .commute 18, .commute
    16])
,
  ([6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 3, 2, 8, 0, 5, 1, 6, 0, 5, 8, 0, 1, 2, 3, 0, 5, 6, 1, 2, 0, 8,
    1, 0, 5, 6, 0, 1, 2, 8, 0, 1, 5, 0, 8, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0], [6,
    5, 0, 1, 2, 8, 3, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 8, 0, 1, 2, 3, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5,
    6, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0],
    [.commute 14, .commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12,
    .commute 13, .braid 14, .braid 16, .braid 18, .commute 20, .commute 21, .commute 22,
    .commute 13, .commute 14, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10,
    .braid 11, .commute 13, .braid 14, .commute 16, .commute 17, .braid 18, .commute 20,
    .commute 21, .braid 22, .commute 24, .commute 25, .commute 26, .commute 27, .braid 28,
    .braid 30, .commute 32, .commute 33, .braid 34, .commute 36, .braid 37, .commute 39,
    .commute 40, .braid 41, .commute 39, .commute 25, .commute 26, .commute 27, .commute 28,
    .commute 29, .commute 30, .braid 31, .commute 24, .commute 25, .commute 9, .commute 10,
    .commute 11, .commute 12, .commute 7, .commute 8, .commute 5, .commute 6, .commute 3,
    .commute 4])
,
  ([6, 5, 0, 1, 2, 8, 3, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 8, 0, 1, 2, 3, 8, 0, 1, 2, 5, 0, 8, 1, 0,
    5, 6, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0], [6,
    5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 8, 0, 1, 2, 5, 0, 1, 8, 0, 5, 6, 5,
    0, 8, 0, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0],
    [.commute 5, .braid 6, .braid 8, .commute 10, .commute 11, .braid 12, .commute 14, .commute
    15, .commute 16, .commute 17, .braid 18, .commute 20, .commute 21, .braid 22, .commute 24,
    .braid 25, .commute 27, .commute 28, .braid 29, .commute 31, .braid 32, .commute 34,
    .commute 35, .commute 36, .braid 37, .braid 39, .commute 41, .commute 35, .commute 36,
    .commute 37, .commute 34, .commute 27, .commute 5, .commute 6, .commute 7, .commute 8,
    .commute 9, .commute 10, .commute 4, .commute 5, .braid 2, .commute 4, .braid 5, .commute 7,
    .commute 8, .commute 9, .braid 10, .commute 12, .commute 13, .commute 14, .commute 15,
    .commute 16, .commute 17, .braid 18, .commute 20, .commute 21, .braid 22, .commute 24,
    .braid 25, .braid 27, .commute 29, .commute 30, .commute 31, .braid 32])
,
  ([6, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 8, 0, 1, 2, 5, 0, 1, 8, 0, 5, 6,
    5, 0, 8, 0, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0], [6,
    5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 5, 0, 1, 2, 3, 8, 0, 5, 1, 2, 0, 8, 1, 0, 1, 5, 6, 5, 0, 8,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0], [.braid
    34, .commute 36, .braid 37, .commute 39, .commute 40, .commute 19, .commute 20, .commute 21,
    .commute 18, .commute 19, .commute 17, .braid 15, .braid 17, .braid 19, .braid 21, .commute
    23, .commute 24, .commute 25, .commute 26, .commute 27, .commute 28, .commute 29, .commute
    30, .commute 31, .commute 32, .commute 33, .commute 34, .commute 35, .commute 22, .commute
    23, .commute 20, .commute 21, .commute 18, .commute 19, .braid 13, .commute 15, .commute 16,
    .commute 17, .commute 18, .braid 19, .braid 21, .braid 23, .commute 25, .commute 26,
    .commute 27, .commute 28, .commute 29, .commute 30, .commute 31, .commute 24, .commute 22,
    .commute 15, .commute 16, .commute 17, .commute 12, .braid 13, .commute 15, .commute 16,
    .braid 17, .commute 19, .commute 20, .commute 21, .braid 22, .braid 24])
,
  ([6, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 5, 0, 1, 2, 3, 8, 0, 5, 1, 2, 0, 8, 1, 0, 1, 5, 6, 5, 0,
    8, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0], [1,
    2, 3, 5, 6, 0, 5, 8, 0, 1, 2, 3, 0, 8, 5, 0, 1, 2, 5, 6, 5, 0, 8, 1, 0, 5, 6, 0, 5, 1, 0, 8,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0],
    [.commute 26, .commute 27, .commute 28, .commute 19, .commute 20, .commute 11, .commute 12,
    .braid 13, .commute 15, .commute 16, .braid 17, .commute 19, .braid 20, .commute 22,
    .commute 23, .braid 24, .commute 26, .commute 9, .commute 8, .braid 9, .commute 11, .commute
    12, .commute 13, .commute 14, .commute 15, .commute 16, .commute 17, .commute 18, .commute
    7, .commute 8, .braid 9, .commute 11, .commute 12, .commute 13, .commute 14, .commute 6,
    .commute 7, .commute 8, .braid 9, .commute 11, .commute 12, .commute 4, .commute 5, .commute
    6, .commute 7, .commute 3, .commute 4, .commute 5, .commute 1, .commute 2, .commute 3,
    .commute 0, .commute 1, .commute 2, .braid 3, .braid 5, .braid 7, .commute 9, .commute 10,
    .commute 11, .braid 12, .braid 14, .commute 16, .commute 17])
,
  ([1, 2, 3, 5, 6, 0, 5, 8, 0, 1, 2, 3, 0, 8, 5, 0, 1, 2, 5, 6, 5, 0, 8, 1, 0, 5, 6, 0, 5, 1, 0,
    8, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0], [1,
    2, 3, 5, 6, 0, 5, 8, 0, 1, 2, 0, 8, 5, 1, 0, 5, 6, 1, 8, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0], [.braid
    18, .commute 20, .commute 21, .commute 22, .commute 23, .braid 24, .braid 26, .braid 28,
    .commute 30, .braid 31, .commute 33, .commute 34, .braid 35, .commute 37, .commute 38,
    .commute 39, .commute 25, .braid 23, .braid 25, .commute 27, .commute 28, .commute 29,
    .commute 26, .commute 24, .commute 22, .commute 23, .braid 24, .braid 26, .commute 28,
    .commute 21, .commute 22, .braid 19, .commute 21, .braid 22, .commute 24, .commute 25,
    .braid 26, .commute 24, .commute 18, .braid 19, .commute 21, .braid 22, .braid 24, .commute
    26, .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .commute 22, .commute
    11, .commute 12, .commute 13, .commute 14, .commute 15, .commute 16, .commute 17, .commute
    18, .commute 19, .commute 20, .commute 21, .braid 14, .commute 16, .commute 17])
,
  ([1, 2, 3, 5, 6, 0, 5, 8, 0, 1, 2, 0, 8, 5, 1, 0, 5, 6, 1, 8, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0], [5,
    1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0],
    [.commute 18, .commute 10, .commute 11, .commute 12, .braid 8, .commute 10, .commute 11,
    .braid 12, .commute 14, .commute 15, .commute 16, .commute 17, .commute 16, .commute 15,
    .commute 10, .commute 11, .commute 12, .braid 13, .commute 6, .commute 7, .braid 8, .commute
    10, .braid 11, .commute 13, .commute 2, .commute 3, .commute 4, .commute 5, .commute 6,
    .commute 7, .commute 8, .commute 1, .commute 2, .commute 3, .commute 4, .commute 2, .commute
    3, .commute 0])
,
  ([5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0, 2],
    [5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 0, 1, 0],
    [.braid 56, .commute 58, .square 59, .commute 55])
,
  ([5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 0, 1, 0, 6], [5,
    1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 0, 1, 0], [.commute 45,
    .commute 46, .commute 47, .commute 44, .commute 45, .commute 43, .braid 41, .braid 43,
    .braid 45, .braid 47, .commute 49, .commute 50, .commute 51, .commute 52, .commute 53,
    .commute 54, .commute 55, .commute 56, .commute 57, .square 58, .commute 46, .commute 44,
    .commute 45, .commute 42, .commute 43, .commute 44, .commute 40, .commute 41, .commute 42,
    .commute 43])
,
  ([5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 0, 1, 0, 3], [5, 1,
    0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1,
    0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 0, 1, 0], [.commute 57,
    .commute 56, .commute 55])
,
  ([5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 0, 1, 0, 0], [5,
    1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 0, 1], [.square 58])
,
  ([5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 0, 1, 1], [5, 1,
    0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1,
    0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 0], [.square 57])
,
  ([5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 0, 5], [5, 1, 0,
    8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0,
    5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [.braid 47, .commute 49,
    .commute 50, .commute 51, .commute 52, .commute 53, .commute 54, .commute 46, .braid 47,
    .commute 49, .commute 50, .commute 51, .commute 52, .commute 53, .braid 54, .square 56,
    .commute 45, .commute 46, .braid 47, .commute 49, .commute 50, .commute 44, .commute 45,
    .commute 46, .braid 47, .commute 49, .braid 50, .commute 52, .commute 53, .commute 52,
    .commute 51, .commute 50, .commute 49, .commute 48, .commute 47, .commute 46, .braid 44])
,
  ([5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0, 8], [5, 1, 0, 8,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 0, 8, 1, 2, 0, 1, 3, 2, 0, 6, 5, 0,
    8, 1, 0, 5, 6, 8, 1, 0, 5, 8, 0, 1, 2, 3, 4, 1, 2, 3, 1, 8, 0, 8], [.commute 39, .braid 37,
    .braid 39, .commute 41, .commute 42, .commute 34, .commute 35, .commute 33, .commute 34,
    .braid 35, .commute 37, .commute 38, .braid 39, .commute 41, .braid 42, .commute 44,
    .commute 30, .commute 31, .commute 32, .commute 33, .commute 29, .commute 30, .commute 31,
    .commute 32, .braid 33, .commute 35, .commute 36, .commute 37, .commute 38, .braid 39,
    .commute 41, .braid 42, .braid 44, .commute 46, .commute 47, .commute 48, .commute 49,
    .commute 50, .commute 51, .commute 52, .commute 53, .commute 36, .commute 26, .braid 24,
    .braid 26, .commute 28, .commute 29, .commute 30, .commute 31, .commute 32, .commute 33,
    .braid 34, .braid 36, .commute 38, .commute 39, .commute 40, .commute 27, .commute 25,
    .commute 23, .commute 24, .braid 25, .braid 27, .commute 29, .commute 30])
,
  ([5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 0, 8, 1, 2, 0, 1, 3, 2,
    0, 6, 5, 0, 8, 1, 0, 5, 6, 8, 1, 0, 5, 8, 0, 1, 2, 3, 4, 1, 2, 3, 1, 8, 0, 8], [5, 1, 0, 8,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 2, 1, 6, 5, 0, 8, 1, 2, 3, 5, 6, 0, 5, 1, 2, 0, 8, 1, 0,
    5, 6, 0, 8, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 0, 1, 2, 3, 1, 8, 0, 8], [.commute 31, .braid 32,
    .commute 34, .commute 35, .braid 36, .commute 38, .commute 34, .commute 28, .commute 26,
    .commute 22, .commute 23, .commute 24, .commute 25, .braid 26, .braid 28, .commute 30,
    .commute 31, .braid 32, .braid 34, .commute 36, .commute 37, .braid 38, .braid 40, .commute
    42, .commute 43, .braid 44, .commute 46, .commute 47, .commute 48, .commute 29, .commute 30,
    .commute 31, .commute 28, .commute 29, .commute 25, .commute 26, .commute 27, .braid 20,
    .commute 22, .commute 23, .commute 24, .commute 25, .commute 17, .commute 18, .commute 16,
    .commute 17, .braid 18, .commute 20, .commute 21, .commute 22, .commute 23, .commute 24,
    .braid 25, .braid 27, .braid 29, .braid 31, .commute 33, .commute 34, .commute 35, .commute
    36, .commute 37, .commute 38, .commute 32, .commute 30])
,
  ([5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 2, 1, 6, 5, 0, 8, 1, 2, 3, 5, 6, 0, 5, 1, 2,
    0, 8, 1, 0, 5, 6, 0, 8, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 0, 1, 2, 3, 1, 8, 0, 8], [5, 1, 0, 8,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 6, 5, 0, 1, 2, 1, 0, 3, 5, 6, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5, 6,
    1, 0, 8, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 8, 0, 8], [.commute 21, .commute
    22, .commute 23, .commute 24, .commute 25, .commute 17, .commute 18, .braid 19, .commute 21,
    .commute 22, .commute 15, .commute 16, .braid 17, .commute 19, .commute 20, .commute 21,
    .braid 22, .commute 24, .braid 25, .commute 27, .commute 28, .commute 29, .braid 30, .braid
    32, .commute 34, .commute 35, .commute 27, .commute 28, .commute 15, .commute 16, .commute
    17, .braid 18, .commute 20, .commute 14, .commute 15, .braid 16, .commute 18, .commute 19,
    .braid 20, .commute 22, .commute 23, .commute 24, .braid 25, .commute 27, .braid 28,
    .commute 30, .commute 31, .braid 32, .commute 34, .braid 35, .commute 37, .braid 38,
    .commute 40, .commute 41, .commute 42, .commute 43, .braid 44, .commute 46, .commute 47,
    .braid 48, .commute 50, .commute 51, .commute 19, .commute 20])
,
  ([5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 6, 5, 0, 1, 2, 1, 0, 3, 5, 6, 8, 0, 1, 2, 5, 0, 8,
    1, 0, 5, 6, 1, 0, 8, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 8, 0, 8], [5, 1, 0, 8,
    6, 2, 1, 3, 0, 1, 2, 5, 0, 1, 8, 0, 5, 6, 5, 0, 8, 1, 2, 3, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 1,
    0, 8, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 8, 0, 8], [.commute 21, .commute
    22, .commute 23, .commute 24, .commute 25, .braid 17, .commute 19, .commute 20, .commute 21,
    .commute 22, .commute 23, .commute 16, .braid 17, .commute 19, .commute 20, .commute 21,
    .commute 15, .commute 16, .braid 17, .commute 19, .commute 13, .commute 14, .commute 15,
    .commute 12, .commute 13, .commute 11, .commute 10, .braid 11, .braid 13, .braid 15,
    .commute 17, .commute 18, .braid 19, .braid 21, .braid 23, .braid 25, .commute 27, .commute
    28, .commute 29, .commute 30, .commute 31, .commute 32, .commute 33, .commute 34, .commute
    35, .commute 36, .commute 26, .commute 27, .commute 28, .commute 24, .commute 25, .commute
    22, .commute 23, .commute 10, .commute 11, .commute 12, .commute 13, .commute 14, .commute
    15, .braid 16, .commute 8, .commute 9, .commute 10, .commute 7])
,
  ([5, 1, 0, 8, 6, 2, 1, 3, 0, 1, 2, 5, 0, 1, 8, 0, 5, 6, 5, 0, 8, 1, 2, 3, 0, 5, 1, 0, 8, 2, 1,
    0, 5, 6, 1, 0, 8, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 8, 0, 8], [5, 1, 6, 2,
    3, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5, 6, 5, 0, 1, 2, 3, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0,
    8, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 0, 1, 2, 1, 3, 0, 1, 8, 0, 8], [.commute 6, .braid 7,
    .commute 9, .braid 10, .commute 12, .commute 13, .braid 14, .commute 16, .braid 17, .commute
    19, .commute 20, .commute 21, .commute 22, .braid 23, .braid 25, .commute 27, .braid 28,
    .commute 30, .commute 31, .commute 32, .commute 19, .commute 20, .commute 21, .commute 12,
    .commute 3, .commute 4, .commute 5, .commute 2, .commute 3, .commute 4, .braid 5, .commute
    7, .commute 8, .commute 9, .braid 10, .braid 12, .commute 14, .commute 15, .commute 16,
    .braid 17, .commute 19, .commute 20, .braid 21, .commute 23, .commute 24, .braid 25,
    .commute 27, .braid 28, .commute 30, .commute 31, .braid 32, .commute 34, .commute 35,
    .braid 36, .commute 38, .commute 39, .commute 40, .commute 41, .commute 42, .commute 43,
    .braid 44, .commute 46, .commute 47, .braid 48])
,
  ([5, 1, 6, 2, 3, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5, 6, 5, 0, 1, 2, 3, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5,
    6, 2, 1, 0, 8, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 0, 1, 2, 1, 3, 0, 1, 8, 0, 8], [5, 1, 6, 2,
    3, 8, 0, 1, 2, 5, 0, 6, 8, 5, 0, 1, 2, 3, 0, 8, 5, 0, 6, 5, 1, 0, 8, 2, 1, 0, 5, 6, 2, 3, 0,
    1, 2, 8, 0, 5, 1, 0, 8, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [.commute 50, .braid 51, .braid
    53, .square 55, .commute 52, .commute 50, .commute 51, .commute 49, .commute 50, .braid 47,
    .commute 49, .commute 46, .commute 47, .commute 48, .commute 45, .commute 46, .commute 47,
    .braid 43, .commute 45, .commute 46, .commute 42, .braid 43, .commute 45, .commute 41,
    .commute 42, .braid 43, .commute 40, .commute 41, .commute 39, .braid 37, .braid 39, .braid
    41, .commute 43, .commute 35, .commute 36, .commute 37, .commute 34, .commute 33, .braid 34,
    .commute 36, .braid 37, .commute 39, .commute 40, .braid 41, .commute 39, .braid 14,
    .commute 16, .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .commute 13,
    .braid 14, .commute 16, .commute 17, .commute 18, .commute 19, .commute 12, .commute 13,
    .braid 14, .commute 16, .commute 17, .commute 11])
,
  ([5, 1, 6, 2, 3, 8, 0, 1, 2, 5, 0, 6, 8, 5, 0, 1, 2, 3, 0, 8, 5, 0, 6, 5, 1, 0, 8, 2, 1, 0, 5,
    6, 2, 3, 0, 1, 2, 8, 0, 5, 1, 0, 8, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [1, 2, 3, 8, 0, 5,
    6, 1, 0, 5, 8, 0, 1, 2, 3, 1, 0, 8, 5, 6, 0, 1, 5, 0, 8, 2, 1, 0, 5, 6, 2, 3, 5, 0, 5, 1, 2,
    8, 0, 5, 1, 0, 8, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [.commute 12, .commute 10, .commute
    2, .commute 3, .commute 4, .commute 5, .commute 6, .commute 7, .braid 8, .braid 10, .braid
    12, .commute 14, .commute 15, .commute 16, .braid 17, .braid 19, .braid 21, .commute 23,
    .commute 24, .commute 25, .commute 26, .commute 27, .commute 28, .braid 29, .commute 31,
    .commute 32, .commute 22, .commute 20, .commute 7, .commute 8, .commute 9, .commute 10,
    .commute 11, .commute 12, .braid 13, .commute 15, .commute 6, .commute 7, .commute 0,
    .commute 1, .commute 2, .commute 3, .braid 4, .commute 6, .braid 7, .commute 9, .commute 10,
    .braid 11, .commute 13, .commute 14, .braid 15, .commute 17, .commute 18, .commute 19,
    .braid 20, .braid 22, .commute 24, .commute 25, .commute 26, .braid 27, .commute 29,
    .commute 30, .commute 31, .braid 32])
,
  ([1, 2, 3, 8, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 3, 1, 0, 8, 5, 6, 0, 1, 5, 0, 8, 2, 1, 0, 5, 6, 2,
    3, 5, 0, 5, 1, 2, 8, 0, 5, 1, 0, 8, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [1, 2, 3, 8, 0, 5,
    6, 1, 0, 5, 8, 0, 1, 2, 1, 0, 8, 3, 6, 5, 0, 1, 2, 3, 5, 6, 0, 5, 8, 0, 1, 2, 0, 8, 5, 6, 0,
    1, 5, 0, 8, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [.commute 34, .commute 35, .commute
    36, .braid 37, .braid 39, .commute 41, .commute 29, .commute 30, .commute 28, .commute 29,
    .braid 30, .commute 32, .commute 33, .commute 34, .commute 35, .commute 36, .commute 27,
    .commute 28, .commute 29, .braid 30, .commute 32, .commute 33, .commute 34, .braid 25,
    .commute 27, .commute 28, .commute 29, .braid 30, .commute 32, .commute 24, .commute 25,
    .commute 26, .commute 27, .commute 28, .commute 21, .braid 22, .commute 24, .commute 25,
    .commute 26, .braid 20, .commute 22, .commute 23, .commute 24, .braid 18, .commute 20,
    .commute 21, .commute 22, .commute 23, .braid 24, .braid 26, .braid 28, .commute 30,
    .commute 31, .braid 32, .braid 34, .braid 36, .commute 38, .commute 39, .commute 40,
    .commute 37, .commute 35, .commute 14, .commute 15, .commute 16])
,
  ([1, 2, 3, 8, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 1, 0, 8, 3, 6, 5, 0, 1, 2, 3, 5, 6, 0, 5, 8, 0, 1,
    2, 0, 8, 5, 6, 0, 1, 5, 0, 8, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [1, 2, 3, 8, 0, 5,
    1, 0, 2, 1, 6, 5, 6, 0, 5, 8, 0, 1, 2, 3, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 1, 0, 5, 6, 8, 0, 1,
    5, 0, 8, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [.commute 17, .commute 18, .commute
    19, .commute 20, .braid 21, .commute 23, .commute 24, .commute 25, .commute 26, .commute 27,
    .commute 28, .braid 29, .braid 12, .commute 14, .commute 15, .commute 16, .commute 17,
    .commute 18, .braid 19, .commute 21, .commute 22, .commute 23, .commute 11, .braid 12,
    .commute 14, .commute 15, .commute 16, .braid 17, .commute 19, .commute 20, .commute 10,
    .commute 11, .braid 12, .commute 14, .braid 15, .commute 17, .commute 18, .commute 19,
    .braid 20, .commute 22, .braid 23, .commute 25, .commute 26, .braid 27, .commute 29, .braid
    30, .commute 32, .commute 33, .commute 34, .braid 35, .braid 37, .commute 39, .commute 32,
    .commute 33, .commute 25, .commute 13, .commute 14, .commute 12, .commute 9, .commute 10,
    .commute 6, .commute 7, .commute 8, .commute 9])
,
  ([1, 2, 3, 8, 0, 5, 1, 0, 2, 1, 6, 5, 6, 0, 5, 8, 0, 1, 2, 3, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 1,
    0, 5, 6, 8, 0, 1, 5, 0, 8, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [1, 2, 3, 8, 1, 0,
    5, 6, 2, 1, 0, 5, 8, 0, 1, 2, 3, 8, 0, 1, 5, 0, 8, 6, 5, 0, 1, 2, 1, 0, 5, 6, 8, 5, 0, 5, 1,
    0, 8, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [.braid 10, .braid 12, .braid 14,
    .commute 16, .commute 17, .commute 18, .commute 9, .commute 10, .commute 7, .commute 5,
    .commute 6, .braid 7, .commute 9, .braid 10, .commute 12, .commute 13, .braid 14, .commute
    16, .commute 17, .braid 18, .commute 20, .commute 21, .commute 22, .braid 23, .braid 25,
    .commute 27, .commute 28, .commute 29, .braid 30, .commute 32, .braid 33, .commute 35,
    .commute 36, .braid 37, .commute 35, .commute 21, .commute 22, .commute 23, .commute 20,
    .commute 6, .commute 7, .commute 8, .braid 4, .commute 6, .commute 7, .braid 8, .commute 10,
    .commute 11, .commute 12, .commute 13, .braid 14, .commute 16, .commute 17, .braid 18,
    .braid 20, .commute 22, .braid 23, .commute 25, .commute 26, .commute 27, .commute 28,
    .commute 29, .braid 30, .commute 32])
,
  ([1, 2, 3, 8, 1, 0, 5, 6, 2, 1, 0, 5, 8, 0, 1, 2, 3, 8, 0, 1, 5, 0, 8, 6, 5, 0, 1, 2, 1, 0, 5,
    6, 8, 5, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [8, 2, 1, 0, 5, 6,
    3, 2, 1, 0, 5, 8, 0, 1, 2, 8, 0, 5, 6, 3, 1, 2, 0, 1, 8, 0, 5, 6, 0, 8, 1, 0, 5, 2, 1, 0, 8,
    2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [.braid 33, .braid 35, .commute 37,
    .braid 26, .commute 28, .commute 29, .commute 30, .commute 31, .commute 32, .commute 33,
    .commute 25, .braid 26, .commute 28, .commute 29, .commute 30, .commute 24, .commute 25,
    .braid 26, .commute 28, .commute 22, .commute 23, .commute 24, .commute 21, .commute 22,
    .commute 19, .commute 20, .commute 2, .commute 3, .commute 4, .commute 5, .commute 6,
    .commute 1, .commute 0, .braid 1, .commute 3, .commute 4, .commute 5, .braid 6, .commute 8,
    .commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .braid 14, .commute 16,
    .commute 17, .commute 18, .commute 19, .braid 20, .braid 22, .braid 24, .commute 26,
    .commute 27, .braid 28, .braid 30, .commute 32, .braid 33, .commute 35, .commute 36,
    .commute 15, .commute 16, .commute 17, .commute 18])
,
  ([8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 8, 0, 1, 2, 8, 0, 5, 6, 3, 1, 2, 0, 1, 8, 0, 5, 6, 0, 8, 1,
    0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [8, 2, 1, 0, 3, 2,
    1, 6, 5, 0, 8, 1, 0, 5, 6, 2, 3, 1, 2, 5, 0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [.commute 19, .commute 14, .commute
    15, .commute 16, .commute 17, .commute 13, .braid 11, .braid 13, .commute 15, .commute 16,
    .braid 17, .braid 19, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25,
    .commute 26, .commute 27, .commute 28, .commute 29, .commute 30, .commute 31, .commute 20,
    .commute 18, .braid 9, .commute 11, .commute 12, .braid 13, .commute 15, .commute 16,
    .commute 17, .braid 18, .braid 20, .commute 22, .commute 23, .commute 24, .commute 25,
    .commute 26, .commute 27, .commute 25, .commute 26, .braid 23, .commute 25, .commute 22,
    .braid 23, .commute 21, .commute 19, .commute 5, .commute 6, .commute 7, .commute 4,
    .commute 5, .commute 6, .braid 7, .commute 9, .commute 10, .commute 11, .commute 12, .braid
    13, .commute 15, .commute 16, .commute 17, .commute 18])
,
  ([8, 2, 1, 0, 3, 2, 1, 6, 5, 0, 8, 1, 0, 5, 6, 2, 3, 1, 2, 5, 0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0,
    5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [8, 6, 2, 1, 0, 5,
    3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0], [.braid 19, .braid 21, .commute 23,
    .commute 18, .commute 19, .commute 16, .commute 17, .commute 18, .commute 6, .commute 7,
    .commute 5, .commute 6, .commute 4, .commute 5, .commute 3, .commute 2, .commute 1])
,
  ([8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0,
    5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 0, 2], [8, 6, 2, 1, 0,
    5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0,
    8, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0], [.commute 54])
,
  ([8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0,
    5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 6], [8, 6, 2, 1,
    0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1,
    0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0], [.commute 41, .commute 42,
    .commute 40, .braid 38, .braid 40, .braid 42, .commute 44, .commute 45, .commute 46,
    .commute 47, .commute 48, .commute 49, .commute 50, .commute 51, .commute 52, .commute 53,
    .commute 54, .square 55, .commute 41, .commute 39, .commute 40, .commute 37, .commute 38,
    .commute 39])
,
  ([8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0,
    5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 3], [8, 6, 2, 1, 0,
    5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0,
    8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 1, 2, 0], [.commute 51, .braid 49, .braid 51,
    .commute 53, .square 54, .commute 50])
,
  ([8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0,
    5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 1, 2, 0, 0], [8, 6, 2, 1, 0, 5,
    3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 1, 2], [.square 53])
,
  ([8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0,
    5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 1, 2, 1], [8, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0,
    5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 1, 2, 1], [])
,
  ([8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0,
    5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 1, 2, 1, 5], [8, 6, 2, 1, 0, 5,
    3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    0, 5, 6, 5, 0, 1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 1], [.braid 42, .commute 44, .commute 45,
    .commute 46, .commute 47, .commute 48, .commute 49, .commute 50, .commute 51, .commute 52,
    .square 53, .commute 41, .braid 42, .commute 44, .commute 45, .commute 46, .commute 47,
    .commute 48, .commute 40, .commute 41, .braid 42, .commute 44, .commute 45])
,
  ([8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0,
    5, 3, 2, 1, 0, 8, 0, 5, 6, 5, 0, 1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 1, 8], [8, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 0, 8, 1, 2, 0, 1, 3, 2, 5, 0, 8, 1, 0, 5, 6, 1, 0, 5,
    8, 0, 1, 0, 2, 3, 4, 1, 2, 3, 8, 0, 1, 2, 1, 8], [.braid 35, .commute 37, .commute 38,
    .commute 39, .commute 31, .commute 32, .commute 33, .commute 34, .braid 35, .commute 37,
    .commute 27, .commute 28, .commute 29, .commute 30, .commute 31, .commute 32, .commute 33,
    .commute 34, .braid 35, .braid 37, .braid 39, .commute 41, .commute 42, .commute 43,
    .commute 44, .commute 45, .commute 46, .commute 47, .commute 32, .commute 29, .commute 30,
    .commute 23, .braid 21, .braid 23, .commute 25, .commute 26, .commute 27, .commute 28,
    .commute 29, .braid 30, .braid 32, .commute 34, .commute 35, .commute 25, .commute 26,
    .commute 27, .commute 28, .commute 24, .commute 22, .commute 20, .commute 21, .braid 22,
    .braid 24, .commute 26, .commute 27, .braid 28, .commute 30, .commute 31, .braid 32,
    .commute 34, .braid 35, .commute 37, .commute 38, .braid 39])
,
  ([8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 0, 8, 1, 2, 0, 1, 3, 2, 5, 0, 8,
    1, 0, 5, 6, 1, 0, 5, 8, 0, 1, 0, 2, 3, 4, 1, 2, 3, 8, 0, 1, 2, 1, 8], [8, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 1, 0, 5, 6, 2, 3, 5, 0, 1, 8, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 2, 1, 0, 5, 8,
    0, 1, 2, 3, 4, 0, 1, 2, 3, 8, 0, 1, 2, 1], [.commute 41, .commute 42, .commute 43, .commute
    27, .commute 28, .commute 29, .commute 25, .commute 26, .commute 24, .commute 18, .commute
    17, .braid 18, .commute 20, .commute 21, .commute 22, .commute 23, .braid 24, .braid 26,
    .commute 28, .braid 29, .commute 31, .commute 32, .commute 33, .commute 20, .commute 21,
    .commute 22, .commute 16, .commute 17, .braid 18, .commute 20, .commute 21, .braid 22,
    .commute 24, .commute 25, .braid 26, .commute 28, .braid 29, .commute 31, .commute 32,
    .braid 33, .commute 35, .commute 36, .commute 37, .commute 38, .braid 39, .commute 41,
    .commute 42, .braid 43, .commute 45, .commute 46, .braid 47, .commute 49, .commute 50,
    .commute 51, .square 52, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25,
    .commute 26, .commute 20, .commute 21, .commute 22])
,
  ([8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 3, 5, 0, 1, 8, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0,
    5, 6, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 0, 1, 2, 3, 8, 0, 1, 2, 1], [8, 6, 2, 1, 3, 2, 5, 0, 1,
    8, 0, 5, 6, 2, 3, 5, 0, 8, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 8, 0, 1, 2,
    0, 3, 8, 4, 1, 2, 3, 0, 1, 2, 0, 1], [.commute 19, .commute 10, .braid 8, .braid 10,
    .commute 12, .commute 13, .commute 14, .commute 15, .commute 16, .braid 17, .braid 19,
    .commute 21, .braid 22, .commute 24, .commute 25, .braid 26, .commute 28, .commute 29,
    .commute 30, .commute 31, .commute 5, .commute 6, .commute 4, .commute 5, .braid 6, .commute
    8, .commute 9, .braid 10, .commute 12, .commute 13, .commute 14, .braid 15, .commute 17,
    .commute 18, .braid 19, .commute 21, .braid 22, .commute 24, .commute 25, .braid 26,
    .commute 28, .commute 29, .commute 30, .braid 31, .commute 33, .commute 34, .commute 35,
    .commute 36, .commute 37, .commute 38, .braid 39, .commute 41, .commute 42, .braid 43,
    .commute 45, .commute 46, .braid 47, .commute 49, .commute 45, .commute 44, .commute 43,
    .commute 41, .commute 42, .commute 40])
,
  ([8, 6, 2, 1, 3, 2, 5, 0, 1, 8, 0, 5, 6, 2, 3, 5, 0, 8, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6,
    3, 2, 1, 0, 5, 8, 0, 1, 2, 0, 3, 8, 4, 1, 2, 3, 0, 1, 2, 0, 1], [8, 6, 2, 1, 3, 2, 5, 0, 1,
    8, 0, 6, 5, 0, 8, 1, 2, 3, 0, 1, 6, 2, 5, 0, 1, 8, 0, 5, 6, 3, 2, 8, 0, 5, 1, 0, 8, 0, 5, 0,
    1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1], [.commute 41, .commute 39, .commute 40, .braid 37,
    .commute 39, .commute 36, .braid 37, .commute 35, .braid 33, .braid 35, .commute 37,
    .commute 24, .commute 25, .commute 26, .commute 23, .commute 24, .commute 22, .commute 14,
    .commute 15, .commute 16, .commute 17, .commute 18, .commute 19, .braid 20, .braid 22,
    .braid 24, .braid 26, .commute 28, .commute 29, .commute 30, .commute 31, .commute 19,
    .commute 20, .commute 21, .commute 22, .commute 18, .commute 19, .commute 13, .commute 14,
    .commute 15, .braid 16, .commute 18, .braid 19, .commute 21, .braid 22, .commute 24,
    .commute 25, .braid 26, .commute 28, .commute 29, .commute 30, .braid 31, .commute 33,
    .commute 34, .braid 35, .commute 33, .braid 11, .commute 13, .commute 14, .commute 15,
    .commute 16, .commute 17, .commute 18, .commute 19])
,
  ([8, 6, 2, 1, 3, 2, 5, 0, 1, 8, 0, 6, 5, 0, 8, 1, 2, 3, 0, 1, 6, 2, 5, 0, 1, 8, 0, 5, 6, 3, 2,
    8, 0, 5, 1, 0, 8, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1], [8, 2, 1, 3, 2, 5, 6, 0, 5,
    1, 0, 8, 0, 1, 2, 5, 0, 3, 1, 6, 5, 0, 2, 3, 1, 2, 0, 8, 5, 6, 0, 1, 5, 0, 8, 6, 1, 0, 5, 0,
    1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1], [.commute 20, .commute 10, .braid 11, .commute 13,
    .commute 14, .commute 15, .commute 16, .commute 9, .commute 10, .braid 11, .commute 8,
    .commute 9, .commute 7, .commute 1, .commute 2, .commute 3, .commute 4, .braid 5, .braid 7,
    .braid 9, .commute 11, .braid 12, .commute 14, .commute 15, .braid 16, .commute 18, .commute
    19, .braid 20, .commute 22, .commute 23, .commute 24, .commute 25, .braid 26, .commute 28,
    .commute 29, .commute 30, .braid 31, .braid 33, .commute 35, .commute 27, .commute 28,
    .commute 29, .commute 30, .commute 26, .commute 27, .commute 28, .commute 25, .commute 26,
    .commute 24, .commute 25, .braid 26, .braid 28, .braid 30, .commute 32, .commute 33,
    .commute 34, .commute 31, .commute 29, .commute 23, .commute 19, .commute 20, .commute 21,
    .commute 15, .commute 16])
,
  ([8, 2, 1, 3, 2, 5, 6, 0, 5, 1, 0, 8, 0, 1, 2, 5, 0, 3, 1, 6, 5, 0, 2, 3, 1, 2, 0, 8, 5, 6, 0,
    1, 5, 0, 8, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1], [8, 2, 1, 3, 2, 5, 6, 0, 5,
    1, 0, 8, 5, 0, 1, 2, 3, 6, 5, 0, 1, 2, 1, 0, 5, 6, 8, 0, 5, 0, 1, 0, 8, 0, 5, 6, 1, 0, 5, 0,
    1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1], [.commute 17, .commute 18, .commute 19, .commute 20,
    .braid 21, .braid 23, .commute 20, .commute 21, .commute 17, .commute 18, .commute 14,
    .commute 15, .commute 16, .commute 17, .braid 18, .commute 20, .braid 21, .commute 23,
    .braid 24, .commute 26, .commute 27, .commute 28, .braid 29, .braid 31, .commute 33,
    .commute 26, .commute 27, .commute 17, .commute 18, .commute 19, .commute 15, .commute 13,
    .commute 14, .braid 15, .commute 17, .commute 18, .braid 19, .commute 21, .commute 22,
    .commute 23, .braid 24, .commute 26, .braid 27, .commute 29, .commute 30, .braid 31,
    .commute 29, .commute 14, .commute 15, .commute 16, .commute 17, .braid 12, .commute 14,
    .commute 15, .commute 16, .braid 17, .commute 19, .commute 20, .commute 21, .commute 22,
    .commute 23, .braid 24, .commute 26, .braid 27])
,
  ([8, 2, 1, 3, 2, 5, 6, 0, 5, 1, 0, 8, 5, 0, 1, 2, 3, 6, 5, 0, 1, 2, 1, 0, 5, 6, 8, 0, 5, 0, 1,
    0, 8, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1], [8, 5, 6, 3, 2, 1, 0, 5, 8,
    0, 1, 2, 3, 6, 1, 2, 0, 1, 0, 8, 0, 5, 6, 0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 1, 0, 5, 0,
    1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1], [.braid 29, .commute 31, .braid 20, .commute 22,
    .commute 23, .commute 24, .commute 25, .commute 26, .commute 27, .commute 19, .braid 20,
    .commute 22, .commute 23, .commute 24, .commute 18, .commute 19, .braid 20, .commute 22,
    .commute 11, .commute 8, .braid 9, .braid 11, .commute 13, .commute 14, .commute 15,
    .commute 16, .commute 17, .commute 18, .braid 7, .commute 9, .commute 10, .braid 11,
    .commute 13, .commute 14, .commute 15, .commute 16, .commute 4, .commute 5, .commute 2,
    .commute 3, .commute 4, .braid 5, .commute 7, .commute 8, .commute 9, .commute 10, .braid
    11, .commute 13, .commute 14, .commute 2, .commute 3, .commute 1, .commute 2, .braid 3,
    .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .braid 11, .commute
    13, .braid 14, .braid 16])
,
  ([8, 5, 6, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 6, 1, 2, 0, 1, 0, 8, 0, 5, 6, 0, 8, 1, 0, 5, 2, 1, 0,
    8, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1], [8, 5, 3, 2, 1, 0, 8, 5, 6,
    2, 1, 3, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 0,
    1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1], [.braid 18, .commute 20, .commute 21, .braid 22, .braid
    24, .commute 26, .braid 27, .commute 29, .commute 30, .commute 12, .commute 13, .commute 11,
    .commute 10, .braid 11, .braid 13, .commute 15, .commute 16, .commute 17, .commute 18,
    .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25,
    .commute 14, .commute 12, .commute 9, .commute 10, .commute 11, .braid 12, .braid 14,
    .commute 16, .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .commute 19,
    .commute 20, .braid 17, .commute 19, .commute 16, .braid 17, .commute 15, .commute 13,
    .commute 7, .commute 2, .commute 3, .commute 4, .commute 5, .commute 6, .braid 7, .commute
    9, .commute 10, .commute 11, .commute 12, .braid 13, .braid 15, .commute 17, .commute 12,
    .commute 13, .commute 10])
,
  ([8, 5, 3, 2, 1, 0, 8, 5, 6, 2, 1, 3, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1], [5, 3, 2, 1, 0, 8, 0, 5, 6,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 0,
    1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1], [.commute 11, .commute 12, .commute 0, .commute 1,
    .commute 2, .commute 3, .braid 4])
,
  ([5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1, 2], [5, 3, 2, 1, 0, 8, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5,
    0, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1], [.commute 49, .braid 47, .braid 49, .square 51,
    .commute 48])
,
  ([5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 6], [5, 3, 2, 1, 0, 8, 0, 5, 6,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1,
    2, 3, 4, 1, 2, 3, 1, 2, 0, 1], [.commute 35, .commute 36, .commute 34, .braid 32, .braid 34,
    .braid 36, .commute 38, .commute 39, .commute 40, .commute 41, .commute 42, .commute 43,
    .commute 44, .commute 45, .commute 46, .commute 47, .commute 48, .commute 49, .square 50,
    .commute 35, .commute 33, .commute 34, .commute 31, .commute 32, .commute 33])
,
  ([5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 3], [5, 3, 2, 1, 0, 8, 0, 5, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2,
    3, 4, 2, 3, 1, 2, 0, 1], [.commute 45, .braid 43, .braid 45, .commute 47, .commute 48,
    .square 49, .commute 44])
,
  ([5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 1, 2, 0, 1, 0], [5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1,
    0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3,
    4, 2, 3, 1, 2, 0, 1, 0], [])
,
  ([5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 1, 2, 0, 1, 0, 1], [5, 3, 2, 1, 0, 8, 0, 5, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 1, 2,
    3, 4, 2, 3, 1, 2, 1, 0], [.braid 47, .square 49])
,
  ([5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 1, 2, 1, 0, 5], [5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1,
    0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 4, 3, 2, 1, 0, 5, 0, 1,
    2, 3, 4, 2, 3, 1, 2, 0], [.braid 36, .commute 38, .commute 39, .commute 40, .commute 41,
    .commute 42, .commute 43, .commute 44, .commute 45, .commute 46, .braid 47, .braid 44,
    .commute 46, .commute 47, .commute 35, .braid 36, .commute 38, .commute 39, .commute 40,
    .commute 41, .commute 42, .commute 43, .braid 44, .commute 46, .braid 41, .commute 43,
    .commute 44, .commute 45, .commute 34, .commute 35, .braid 36, .commute 38, .commute 39,
    .commute 40, .braid 41, .commute 43, .commute 44, .braid 38, .commute 40, .commute 41,
    .commute 42, .commute 43, .commute 37, .braid 38, .commute 40, .commute 41, .commute 42,
    .commute 36, .commute 37, .braid 38, .commute 40, .commute 41, .commute 35, .commute 36,
    .commute 37, .braid 38, .commute 40, .commute 34, .commute 35, .commute 36, .commute 37,
    .braid 38])
,
  ([5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    0, 5, 6, 4, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 3, 1, 2, 0, 8], [5, 3, 2, 1, 0, 8, 0, 5, 6, 2,
    1, 0, 5, 3, 2, 0, 1, 8, 0, 5, 6, 2, 1, 3, 2, 0, 8, 1, 0, 5, 1, 6, 4, 2, 3, 0, 1, 2, 8, 0, 1,
    5, 0, 8, 5, 1, 2, 3, 4, 3, 2], [.commute 48, .commute 49, .commute 46, .commute 47, .commute
    48, .commute 44, .commute 45, .commute 46, .commute 47, .braid 42, .commute 44, .commute 45,
    .commute 46, .commute 41, .braid 42, .commute 44, .commute 45, .commute 40, .commute 41,
    .braid 42, .commute 44, .commute 39, .commute 40, .commute 41, .commute 38, .commute 39,
    .commute 37, .braid 35, .braid 37, .braid 39, .braid 41, .commute 43, .braid 29, .commute
    31, .commute 32, .commute 33, .commute 34, .commute 35, .commute 36, .commute 37, .commute
    25, .commute 26, .commute 27, .commute 28, .braid 29, .commute 31, .commute 32, .commute 33,
    .commute 34, .commute 27, .commute 24, .commute 25, .commute 17, .braid 15, .braid 17,
    .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .braid 25,
    .braid 27, .commute 29])
,
  ([5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 0, 1, 8, 0, 5, 6, 2, 1, 3, 2, 0, 8, 1, 0, 5, 1,
    6, 4, 2, 3, 0, 1, 2, 8, 0, 1, 5, 0, 8, 5, 1, 2, 3, 4, 3, 2], [5, 3, 2, 1, 0, 8, 0, 5, 6, 2,
    1, 3, 5, 0, 8, 1, 2, 3, 0, 1, 5, 0, 8, 2, 1, 0, 5, 6, 4, 0, 1, 2, 3, 5, 0, 1, 2, 8, 0, 5, 1,
    0, 8, 0, 5, 1, 2, 3, 4, 3, 2], [.commute 30, .commute 31, .commute 24, .commute 25, .commute
    22, .commute 12, .commute 13, .commute 11, .commute 12, .braid 13, .commute 15, .commute 16,
    .braid 17, .commute 19, .commute 20, .commute 21, .braid 22, .commute 24, .braid 25,
    .commute 27, .commute 28, .commute 29, .commute 30, .braid 31, .commute 33, .braid 34,
    .commute 36, .braid 37, .commute 39, .commute 40, .braid 41, .commute 39, .commute 19,
    .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25, .commute 26,
    .braid 27, .commute 29, .commute 30, .commute 31, .commute 32, .commute 18, .commute 19,
    .commute 20, .commute 17, .commute 18, .commute 15, .commute 12, .commute 13, .commute 14,
    .braid 15, .commute 17, .braid 18, .braid 20, .commute 22, .commute 23, .commute 24, .braid
    25, .commute 27, .commute 28])
,
  ([5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 3, 5, 0, 8, 1, 2, 3, 0, 1, 5, 0, 8, 2, 1, 0, 5, 6, 4, 0, 1,
    2, 3, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 0, 5, 1, 2, 3, 4, 3, 2], [5, 3, 2, 1, 0, 8, 0, 5, 6, 5,
    0, 1, 2, 3, 8, 0, 1, 2, 5, 0, 1, 8, 0, 5, 6, 4, 8, 0, 8, 1, 2, 3, 5, 0, 8, 1, 0, 5, 2, 1, 0,
    8, 1, 0, 5, 1, 2, 3, 4, 3, 2], [.commute 14, .commute 15, .commute 16, .commute 10, .commute
    11, .braid 12, .commute 14, .commute 15, .braid 16, .commute 18, .commute 19, .braid 20,
    .commute 22, .braid 23, .commute 25, .commute 26, .commute 27, .braid 28, .commute 30,
    .commute 31, .braid 32, .commute 34, .commute 35, .commute 36, .braid 37, .braid 39,
    .commute 41, .commute 35, .commute 36, .commute 37, .commute 34, .commute 21, .commute 22,
    .commute 20, .commute 18, .commute 10, .commute 11, .commute 12, .braid 13, .commute 15,
    .commute 16, .commute 17, .braid 18, .braid 20, .braid 22, .commute 24, .commute 25,
    .commute 26, .commute 17, .commute 18, .commute 9, .commute 10, .braid 11, .commute 13,
    .commute 14, .braid 15, .commute 17, .braid 18, .commute 20, .commute 21, .braid 22,
    .commute 24, .commute 25, .braid 26])
,
  ([5, 3, 2, 1, 0, 8, 0, 5, 6, 5, 0, 1, 2, 3, 8, 0, 1, 2, 5, 0, 1, 8, 0, 5, 6, 4, 8, 0, 8, 1, 2,
    3, 5, 0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 1, 2, 3, 4, 3, 2], [5, 3, 2, 1, 8, 0, 5, 6, 5, 0,
    8, 1, 0, 2, 1, 3, 2, 5, 0, 1, 0, 8, 5, 0, 1, 6, 5, 6, 0, 8, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8,
    2, 1, 0, 5, 1, 2, 3, 4, 3, 2], [.commute 28, .commute 29, .commute 30, .commute 31, .braid
    32, .braid 34, .commute 36, .braid 37, .commute 39, .commute 40, .commute 30, .commute 31,
    .commute 32, .commute 33, .commute 34, .commute 35, .commute 25, .commute 26, .commute 27,
    .commute 28, .commute 29, .commute 30, .commute 31, .commute 32, .commute 33, .commute 34,
    .commute 28, .commute 29, .commute 30, .commute 13, .commute 14, .commute 15, .commute 12,
    .commute 13, .commute 11, .braid 4, .commute 6, .commute 7, .commute 8, .braid 9, .braid 11,
    .braid 13, .braid 15, .commute 17, .commute 18, .commute 19, .commute 20, .commute 21,
    .commute 22, .commute 23, .commute 24, .commute 25, .commute 26, .commute 27, .commute 28,
    .commute 29, .commute 23, .commute 24, .commute 25, .commute 22, .braid 20, .braid 22,
    .commute 24, .braid 25])
,
  ([5, 3, 2, 1, 8, 0, 5, 6, 5, 0, 8, 1, 0, 2, 1, 3, 2, 5, 0, 1, 0, 8, 5, 0, 1, 6, 5, 6, 0, 8, 3,
    2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 1, 2, 3, 4, 3, 2], [5, 3, 2, 1, 8, 6, 5, 0, 1, 2,
    3, 2, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8,
    2, 1, 0, 5, 1, 2, 3, 4, 3, 2], [.commute 27, .commute 28, .braid 18, .commute 20, .commute
    21, .braid 22, .commute 24, .braid 25, .commute 27, .commute 20, .commute 17, .braid 18,
    .braid 20, .commute 22, .commute 23, .commute 24, .braid 25, .commute 22, .commute 23,
    .commute 21, .commute 19, .braid 6, .commute 8, .commute 9, .commute 10, .commute 11,
    .commute 12, .commute 13, .commute 14, .commute 15, .commute 16, .commute 17, .commute 18,
    .braid 19, .braid 21, .braid 23, .commute 25, .commute 13, .braid 14, .commute 16, .commute
    17, .commute 18, .commute 19, .commute 20, .commute 21, .commute 11, .commute 12, .commute
    13, .braid 14, .commute 16, .commute 17, .commute 18, .commute 9, .commute 10, .commute 11,
    .commute 12, .commute 13, .braid 14, .commute 5, .braid 6, .commute 8, .commute 9, .commute
    10, .commute 11])
,
  ([5, 3, 2, 1, 8, 6, 5, 0, 1, 2, 3, 2, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 3,
    2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 1, 2, 3, 4, 3, 2], [5, 8, 6, 2, 3, 1, 2, 0, 5, 0,
    1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8,
    2, 1, 0, 5, 1, 2, 3, 4, 3, 2], [.commute 12, .commute 3, .commute 4, .commute 5, .braid 6,
    .commute 8, .commute 9, .commute 10, .commute 2, .commute 3, .commute 4, .commute 5, .braid
    6, .commute 8, .commute 1, .commute 2, .commute 3, .commute 4, .commute 5, .braid 6, .braid
    8, .braid 10, .braid 12, .commute 14, .braid 15, .commute 17, .braid 18, .commute 20, .braid
    21, .commute 23, .commute 24, .commute 7, .braid 5, .braid 7, .commute 9, .commute 10,
    .commute 11, .commute 12, .commute 13, .commute 14, .commute 15, .commute 16, .commute 17,
    .commute 18, .commute 19, .commute 8, .commute 6, .commute 4, .commute 5, .braid 6, .braid
    8, .commute 10, .commute 11, .commute 12, .commute 13, .commute 14, .commute 15, .commute 9,
    .commute 7, .commute 3, .commute 4, .commute 5, .commute 6, .braid 7])
,
  ([5, 8, 6, 2, 3, 1, 2, 0, 5, 0, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3,
    2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 1, 2, 3, 4, 3, 2], [8, 5, 6, 2, 1, 0, 5, 3, 2, 1,
    0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8,
    2, 1, 0, 5, 1, 2, 3, 4, 3, 2], [.braid 9, .commute 11, .commute 6, .commute 7, .commute 4,
    .commute 5, .commute 6, .commute 0])
,
  ([8, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3,
    2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 1, 2, 3, 4, 3, 2, 2], [8, 5, 6, 2, 1, 0, 5, 3, 2,
    1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0,
    8, 2, 1, 0, 5, 1, 2, 3, 4, 3], [.square 50])
,
  ([8, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3,
    2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 1, 2, 3, 4, 3, 6], [8, 5, 6, 2, 1, 0, 5, 3, 2, 1,
    0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8,
    2, 1, 0, 5, 6, 1, 2, 3, 4, 3], [.commute 49, .commute 48, .commute 47, .commute 46, .commute
    45])
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
