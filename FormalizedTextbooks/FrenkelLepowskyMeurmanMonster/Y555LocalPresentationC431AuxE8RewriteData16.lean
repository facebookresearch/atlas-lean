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
/-- Exact bounded chunks of literal E8 square, commutation and braid moves, block 16. -/
def y431AuxE8RewriteData16 : Fin 64 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
![
  ([8, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 3, 4, 1, 0, 5, 6, 8, 0, 1, 2, 3, 5, 0, 1, 2, 8, 0, 5, 6, 1,
    0, 8, 0, 5, 1, 0, 2, 1, 2, 3, 2, 8, 0, 5, 6, 1, 0, 5, 0, 8, 1, 0, 5, 6, 2, 1, 4, 3, 2, 0, 1,
    8, 0, 5, 6, 0, 8, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 0], [8, 0, 5, 6, 1, 0, 8,
    5, 0, 1, 2, 3, 4, 1, 0, 5, 6, 8, 0, 1, 2, 3, 5, 0, 1, 2, 0, 8, 5, 0, 1, 2, 3, 6, 5, 0, 6, 8,
    1, 0, 5, 6, 2, 1, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 4, 3, 2, 0, 1, 8, 0, 5, 6, 0, 8, 1,
    0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 4, 3,
    2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 0], [.braid 39, .commute 41, .commute 42,
    .commute 43, .commute 44, .commute 45, .commute 46, .commute 47, .commute 48, .commute 49,
    .commute 50, .commute 51, .commute 52, .commute 53, .commute 40, .commute 41, .commute 42,
    .commute 43, .commute 38, .commute 39, .commute 36, .commute 37, .braid 31, .commute 33,
    .commute 34, .commute 35, .commute 36, .braid 37, .braid 39, .commute 41, .commute 42,
    .braid 43, .commute 45, .commute 46, .commute 47, .commute 48, .commute 33, .commute 34,
    .commute 35, .commute 30, .braid 31, .commute 33, .commute 34, .braid 35, .commute 37,
    .commute 38, .braid 39, .commute 41, .commute 42, .braid 43, .commute 45, .commute 29,
    .commute 30, .commute 31, .commute 32, .commute 33, .commute 28, .braid 26, .braid 28,
    .commute 30, .commute 31, .commute 32, .braid 33, .commute 35])
,
  ([8, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 3, 4, 1, 0, 5, 6, 8, 0, 1, 2, 3, 5, 0, 1, 2, 0, 8, 5, 0, 1,
    2, 3, 6, 5, 0, 6, 8, 1, 0, 5, 6, 2, 1, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 4, 3, 2, 0, 1,
    8, 0, 5, 6, 0, 8, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 0], [8, 0, 5, 6, 1, 0, 8,
    5, 0, 1, 2, 3, 4, 1, 0, 5, 6, 8, 0, 1, 2, 3, 5, 0, 1, 0, 8, 5, 0, 1, 2, 3, 6, 5, 0, 1, 0, 8,
    0, 5, 6, 2, 0, 1, 5, 0, 8, 2, 1, 0, 5, 6, 3, 4, 2, 1, 0, 3, 2, 1, 8, 0, 5, 6, 0, 8, 2, 1, 0,
    5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 4, 3,
    2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 0], [.commute 36, .commute 37, .commute 38,
    .braid 39, .commute 41, .commute 42, .braid 43, .braid 45, .commute 47, .braid 48, .commute
    50, .commute 51, .commute 52, .braid 53, .commute 55, .braid 56, .commute 58, .commute 59,
    .commute 60, .commute 61, .commute 62, .commute 63, .commute 64, .commute 65, .commute 66,
    .commute 67, .commute 68, .commute 69, .commute 58, .commute 55, .commute 56, .commute 44,
    .braid 42, .braid 44, .commute 46, .commute 47, .commute 48, .braid 49, .commute 51,
    .commute 52, .commute 53, .commute 54, .commute 55, .braid 56, .braid 58, .commute 60,
    .commute 61, .commute 62, .commute 63, .commute 64, .commute 65, .commute 55, .commute 56,
    .commute 53, .commute 36, .commute 25, .commute 26, .commute 27, .commute 28, .braid 29,
    .commute 31, .commute 32, .commute 33, .braid 34])
,
  ([8, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 3, 4, 1, 0, 5, 6, 8, 0, 1, 2, 3, 5, 0, 1, 0, 8, 5, 0, 1, 2,
    3, 6, 5, 0, 1, 0, 8, 0, 5, 6, 2, 0, 1, 5, 0, 8, 2, 1, 0, 5, 6, 3, 4, 2, 1, 0, 3, 2, 1, 8, 0,
    5, 6, 0, 8, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 0], [8, 0, 5, 6, 1, 0, 8,
    5, 0, 1, 2, 3, 4, 1, 0, 5, 6, 8, 0, 1, 2, 3, 5, 1, 0, 8, 5, 0, 1, 2, 3, 6, 5, 0, 1, 2, 0, 8,
    5, 0, 1, 6, 5, 0, 8, 2, 1, 0, 5, 6, 5, 3, 4, 2, 1, 3, 2, 0, 5, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0,
    5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 4, 3,
    2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 0], [.braid 36, .commute 38, .commute 39,
    .commute 40, .braid 23, .commute 25, .commute 26, .braid 27, .commute 29, .commute 30,
    .commute 31, .braid 32, .commute 34, .commute 35, .braid 36, .commute 38, .commute 39,
    .braid 40, .commute 42, .commute 43, .braid 44, .commute 46, .braid 47, .commute 49,
    .commute 50, .commute 51, .commute 52, .braid 53, .commute 55, .braid 56, .commute 58,
    .commute 59, .commute 60, .commute 61, .commute 62, .commute 63, .commute 64, .commute 62,
    .commute 63, .braid 60, .commute 62, .commute 59, .braid 60, .commute 58, .commute 55,
    .commute 56, .commute 38, .commute 39, .commute 40, .commute 41, .commute 37, .commute 38,
    .commute 36, .commute 35, .braid 36, .braid 38, .commute 40, .braid 41, .commute 43,
    .commute 44, .commute 45, .commute 46, .commute 47, .braid 48])
,
  ([8, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 3, 4, 1, 0, 5, 6, 8, 0, 1, 2, 3, 5, 1, 0, 8, 5, 0, 1, 2, 3,
    6, 5, 0, 1, 2, 0, 8, 5, 0, 1, 6, 5, 0, 8, 2, 1, 0, 5, 6, 5, 3, 4, 2, 1, 3, 2, 0, 5, 1, 0, 8,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 0], [8, 0, 5, 6, 1, 0, 8,
    5, 0, 1, 2, 3, 4, 1, 0, 5, 6, 8, 0, 5, 2, 1, 0, 8, 5, 0, 1, 2, 3, 6, 5, 0, 1, 2, 1, 0, 8, 5,
    0, 1, 6, 5, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0,
    5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 4, 3,
    2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 0], [.commute 50, .commute 51, .commute 52,
    .commute 53, .commute 54, .commute 55, .braid 56, .braid 58, .commute 60, .commute 55,
    .commute 56, .commute 53, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25,
    .commute 26, .commute 27, .braid 28, .commute 30, .commute 31, .commute 32, .braid 33,
    .commute 20, .commute 19, .braid 20, .commute 22, .commute 23, .commute 24, .commute 25,
    .braid 26, .commute 28, .commute 29, .commute 30, .braid 31, .commute 33, .braid 34,
    .commute 36, .commute 37, .braid 38, .commute 40, .braid 41, .commute 43, .commute 44,
    .commute 45, .braid 46, .commute 48, .commute 49, .commute 50, .commute 51, .commute 52,
    .braid 53, .commute 55, .braid 56, .commute 58, .commute 59, .commute 52, .commute 53,
    .commute 54, .commute 50, .commute 51, .commute 52, .commute 53])
,
  ([8, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 3, 4, 1, 0, 5, 6, 8, 0, 5, 2, 1, 0, 8, 5, 0, 1, 2, 3, 6, 5,
    0, 1, 2, 1, 0, 8, 5, 0, 1, 6, 5, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 0], [8, 0, 5, 6, 1, 0, 8,
    5, 0, 2, 1, 0, 5, 6, 8, 0, 5, 3, 2, 1, 0, 8, 5, 0, 1, 6, 5, 0, 3, 4, 3, 2, 1, 0, 8, 5, 0, 6,
    5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0,
    5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 4, 3,
    2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 0], [.commute 39, .commute 40, .braid 32,
    .commute 34, .commute 35, .commute 36, .commute 37, .commute 38, .commute 39, .commute 28,
    .commute 29, .commute 30, .commute 27, .commute 28, .commute 29, .braid 30, .commute 32,
    .commute 33, .commute 34, .commute 35, .commute 36, .commute 37, .commute 38, .commute 12,
    .commute 13, .commute 14, .commute 15, .commute 16, .commute 17, .commute 18, .commute 19,
    .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25, .commute 26,
    .commute 27, .commute 28, .commute 11, .commute 12, .commute 13, .commute 14, .commute 15,
    .commute 16, .commute 17, .braid 9, .commute 11, .commute 12, .commute 13, .commute 14,
    .commute 15, .commute 16, .braid 17, .commute 19, .commute 20, .commute 21, .commute 22,
    .commute 23, .commute 24, .commute 25, .commute 26, .commute 27])
,
  ([8, 0, 5, 6, 1, 0, 8, 5, 0, 2, 1, 0, 5, 6, 8, 0, 5, 3, 2, 1, 0, 8, 5, 0, 1, 6, 5, 0, 3, 4, 3,
    2, 1, 0, 8, 5, 0, 6, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 0], [8, 0, 5, 6, 1, 0, 8,
    5, 2, 1, 0, 5, 1, 8, 3, 2, 1, 0, 8, 5, 6, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5,
    4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0,
    5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 4, 3,
    2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 0], [.braid 28, .commute 30, .commute 31,
    .commute 32, .commute 33, .commute 34, .commute 35, .commute 36, .commute 37, .commute 35,
    .commute 27, .commute 28, .commute 29, .braid 30, .commute 32, .commute 33, .commute 34,
    .commute 24, .commute 25, .commute 26, .commute 27, .braid 28, .commute 30, .commute 31,
    .commute 32, .commute 33, .commute 21, .commute 16, .commute 17, .commute 18, .braid 19,
    .braid 21, .commute 23, .commute 24, .commute 25, .commute 26, .commute 27, .commute 28,
    .braid 29, .commute 22, .commute 20, .commute 13, .commute 14, .commute 15, .commute 16,
    .commute 17, .commute 18, .commute 19, .braid 20, .braid 22, .commute 24, .commute 25,
    .commute 26, .braid 27, .commute 29, .commute 14, .commute 15, .braid 16, .commute 18,
    .commute 19, .commute 20, .commute 8, .braid 9, .commute 11])
,
  ([8, 0, 5, 6, 1, 0, 8, 5, 2, 1, 0, 5, 1, 8, 3, 2, 1, 0, 8, 5, 6, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 0], [8, 0, 5, 1, 0, 8, 6,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5,
    4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0,
    5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 4, 3,
    2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 0], [.commute 12, .commute 13, .braid 14,
    .commute 16, .commute 17, .commute 18, .commute 19, .commute 12, .commute 13, .commute 14,
    .braid 15, .commute 7, .commute 8, .braid 9, .commute 11, .commute 12, .braid 13, .commute
    15, .commute 3, .commute 4, .commute 5])
,
  ([8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 1, 2, 0, 1, 0, 2], [8, 0, 5, 1, 0, 8,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0,
    5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1,
    0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 4,
    3, 2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1, 0], [.commute 115, .commute 112, .braid
    113, .braid 111, .commute 113])
,
  ([8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3,
    2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1, 0, 6], [8, 0, 5, 1, 0,
    8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1,
    0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2,
    1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5,
    6, 4, 3, 2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1, 0], [.commute 116, .commute 115,
    .commute 114, .commute 113, .commute 112, .commute 111, .commute 110, .commute 109, .commute
    108, .commute 107, .commute 106, .commute 105, .commute 104, .commute 97, .commute 98,
    .commute 99, .commute 100, .commute 101, .braid 102, .commute 96, .commute 97, .commute 98,
    .commute 99, .braid 100, .commute 102, .commute 95, .commute 96, .commute 97, .braid 98,
    .commute 100, .commute 101, .commute 94, .commute 95, .braid 96, .commute 98, .commute 99,
    .commute 100, .commute 93, .braid 94, .commute 96, .commute 97, .commute 98, .commute 99,
    .braid 92, .commute 94, .commute 95, .commute 96, .commute 97, .commute 98])
,
  ([8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 4,
    3, 2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 1, 2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1, 0, 3], [8, 0, 5, 1,
    0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2,
    1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3,
    2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0,
    5, 6, 4, 3, 2, 1, 0, 5, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 0, 1, 0], [.commute 117, .commute
    116, .commute 115, .commute 111, .commute 112, .braid 113, .commute 110, .braid 111,
    .commute 113, .braid 109, .commute 111, .commute 112])
,
  ([8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 4,
    3, 2, 1, 0, 5, 6, 4, 3, 2, 1, 0, 5, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 0, 1, 0, 4], [8, 0, 5,
    1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6,
    2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6,
    3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 4, 3, 2, 1,
    0, 5, 6, 4, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 0, 1, 0], [.commute 118,
    .commute 117, .commute 116, .commute 115, .commute 114, .commute 113, .commute 108, .commute
    109, .commute 110, .braid 111, .commute 107, .commute 108, .braid 109, .commute 111,
    .commute 106, .braid 107, .commute 109, .commute 110, .braid 105, .commute 107, .commute
    108, .commute 109])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1,
    2, 1, 0, 4], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6,
    1, 0, 5, 4, 0, 1, 2, 1, 0], [.commute 33, .commute 32, .commute 31, .commute 30, .commute
    29])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 4, 0,
    1, 2, 1, 0, 1, 2, 1], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1,
    0, 5, 6, 1, 0, 5, 4, 1, 2, 1, 0], [.braid 31, .commute 33, .commute 30, .braid 31, .braid
    33, .square 35, .square 34, .commute 32, .braid 30])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 4, 1,
    2, 1, 0, 6], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1,
    0, 5, 4, 1, 2, 1, 0], [.commute 25, .commute 26, .commute 24, .braid 22, .braid 24, .braid
    26, .commute 28, .commute 29, .commute 30, .commute 31, .commute 32, .square 33, .commute
    25, .commute 23, .commute 24, .commute 21, .commute 22, .commute 23])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 4, 1, 2,
    1, 0, 3], [8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0,
    5, 4, 1, 2, 3, 1, 0], [.commute 32, .commute 31])
,
  ([8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 4, 1, 2,
    3, 1, 0, 0, 8, 0], [8, 0, 5, 6, 1, 0, 2, 8, 0, 1, 5, 0, 8, 2, 1, 0, 5, 6, 0, 1, 2, 5, 0, 1,
    8, 0, 5, 4, 1, 2, 3, 1, 0], [.square 33, .braid 19, .commute 21, .commute 22, .commute 23,
    .commute 24, .commute 16, .commute 17, .commute 18, .braid 19, .commute 21, .commute 22,
    .commute 17, .commute 15, .braid 9, .commute 11, .commute 12, .commute 13, .commute 14,
    .braid 15, .braid 17, .commute 19, .commute 20, .commute 14, .commute 15, .commute 6,
    .commute 7, .commute 8, .braid 9, .commute 11, .braid 12, .commute 14, .braid 15, .commute
    17, .commute 18, .commute 19, .braid 20, .braid 22, .braid 24, .commute 26, .commute 27,
    .commute 28, .commute 29, .commute 30, .commute 31, .square 32, .commute 11, .commute 12,
    .commute 13, .commute 14, .commute 15, .commute 16, .braid 17, .commute 19, .commute 20,
    .commute 10, .commute 7, .braid 8, .braid 10, .commute 12, .commute 13, .commute 14, .braid
    15, .commute 17])
,
  ([8, 0, 5, 6, 1, 0, 2, 8, 0, 1, 5, 0, 8, 2, 1, 0, 5, 6, 0, 1, 2, 5, 0, 1, 8, 0, 5, 4, 1, 2, 3,
    1, 0], [0, 8, 5, 0, 1, 2, 6, 5, 6, 0, 1, 8, 0, 5, 6, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 4, 0, 1,
    2, 3, 0, 1, 0], [.commute 5, .braid 6, .commute 8, .commute 9, .braid 10, .commute 12,
    .braid 13, .commute 15, .commute 16, .braid 17, .commute 19, .braid 20, .commute 22,
    .commute 23, .braid 24, .commute 26, .commute 22, .commute 11, .commute 12, .commute 10,
    .commute 8, .commute 5, .commute 6, .commute 7, .braid 8, .braid 10, .braid 12, .commute 14,
    .commute 15, .commute 7, .commute 8, .commute 4, .braid 5, .commute 7, .braid 8, .commute
    10, .commute 11, .braid 12, .commute 14, .braid 15, .commute 17, .commute 18, .commute 19,
    .braid 20, .braid 22, .commute 24, .commute 25, .braid 26, .commute 28, .commute 29,
    .commute 18, .commute 19, .commute 20, .commute 17, .commute 3, .commute 4, .commute 5,
    .commute 6, .commute 2, .braid 0, .braid 2, .commute 4, .commute 5, .braid 6])
,
  ([0, 8, 5, 0, 1, 2, 6, 5, 6, 0, 1, 8, 0, 5, 6, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 4, 0, 1, 2, 3, 0,
    1, 0], [0, 8, 5, 2, 1, 0, 5, 6, 1, 8, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 4, 0, 1, 2,
    3, 0, 1], [.commute 8, .commute 9, .commute 10, .commute 11, .braid 12, .commute 14, .braid
    15, .braid 17, .commute 19, .braid 20, .commute 22, .commute 23, .commute 24, .commute 25,
    .braid 26, .commute 28, .braid 29, .square 31, .commute 13, .commute 14, .commute 12, .braid
    10, .braid 12, .braid 14, .commute 16, .commute 17, .commute 18, .commute 15, .commute 13,
    .braid 8, .commute 10, .commute 11, .commute 12, .braid 13, .braid 15, .commute 17, .commute
    10, .commute 11, .commute 7, .braid 8, .commute 10, .braid 11, .commute 13, .commute 14,
    .braid 15, .commute 13, .commute 6, .commute 7, .braid 8, .commute 10, .braid 11, .braid 13,
    .commute 15, .braid 4, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .commute
    11, .commute 3, .braid 4, .commute 6, .commute 7])
,
  ([0, 8, 5, 2, 1, 0, 5, 6, 1, 8, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 4, 0, 1, 2, 3, 0,
    1], [0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 4, 0, 1, 2, 3,
    0, 1], [.commute 8, .commute 7, .commute 6, .commute 1, .commute 2, .commute 3, .braid 4])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 4, 0, 1, 2, 3, 0, 1,
    6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0,
    5, 6], [0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 4, 8, 6, 5, 0, 1, 2, 3, 6, 1, 0, 5, 6,
    0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6],
    [.commute 23, .commute 22, .braid 23, .commute 25, .commute 26, .commute 27, .commute 21,
    .commute 22, .braid 23, .commute 25, .commute 26, .braid 27, .commute 29, .commute 19,
    .commute 20, .commute 18, .commute 19, .braid 20, .commute 22, .commute 23, .commute 24,
    .commute 25, .commute 17, .commute 18, .commute 19, .braid 20, .commute 22, .commute 23,
    .commute 24, .braid 25, .commute 27, .commute 28, .braid 29, .square 31, .commute 17,
    .commute 18, .commute 19, .commute 20, .braid 21, .commute 23, .commute 24, .commute 25,
    .braid 26, .commute 16, .commute 17, .commute 18, .braid 19, .commute 21, .commute 22,
    .commute 23, .braid 24, .commute 26, .braid 27, .commute 29, .square 30, .braid 25, .commute
    27, .commute 28, .commute 29, .square 30, .commute 24, .braid 25, .commute 27, .commute 15])
,
  ([0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 4, 8, 6, 5, 0, 1, 2, 3, 6, 1, 0, 5, 6, 0, 8, 0,
    5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [0, 5, 2,
    1, 0, 8, 4, 1, 0, 5, 6, 2, 1, 0, 5, 8, 0, 1, 2, 3, 0, 1, 8, 0, 6, 5, 6, 0, 8, 5, 6, 2, 1, 0,
    5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [.commute 16, .commute
    17, .commute 14, .commute 15, .commute 11, .commute 12, .commute 13, .commute 8, .commute 9,
    .commute 10, .commute 11, .commute 12, .braid 13, .braid 15, .braid 17, .commute 19,
    .commute 20, .commute 21, .commute 22, .commute 23, .commute 11, .commute 12, .commute 13,
    .commute 9, .commute 10, .commute 7, .commute 8, .commute 9, .braid 10, .commute 12, .braid
    13, .commute 15, .commute 16, .braid 17, .commute 19, .commute 20, .commute 21, .commute 8,
    .commute 9, .commute 10, .commute 11, .commute 7, .commute 6, .braid 7, .commute 9, .commute
    10, .braid 11, .commute 13, .commute 14, .commute 15, .commute 16, .braid 17, .commute 19,
    .commute 20, .braid 21, .braid 23, .commute 25, .commute 26, .braid 27, .square 29, .commute
    20, .commute 21, .commute 22, .commute 23])
,
  ([0, 5, 2, 1, 0, 8, 4, 1, 0, 5, 6, 2, 1, 0, 5, 8, 0, 1, 2, 3, 0, 1, 8, 0, 6, 5, 6, 0, 8, 5, 6,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [2, 4, 5, 0, 1,
    8, 0, 5, 6, 2, 1, 0, 8, 0, 5, 1, 0, 2, 1, 8, 0, 6, 5, 2, 0, 8, 3, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [.braid 24, .commute 14, .commute 5,
    .commute 6, .commute 4, .commute 3, .braid 4, .braid 6, .commute 8, .commute 9, .commute 10,
    .commute 11, .braid 12, .braid 14, .commute 16, .commute 17, .commute 18, .commute 1,
    .commute 2, .commute 0, .commute 1, .braid 2, .commute 4, .commute 5, .braid 6, .commute 8,
    .commute 9, .braid 10, .commute 12, .commute 13, .braid 14, .commute 16, .commute 17, .braid
    18, .commute 20, .commute 21, .braid 22, .commute 24, .braid 25, .commute 27, .square 28,
    .braid 23, .commute 25, .commute 26, .square 27, .commute 17, .commute 18, .commute 19,
    .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25, .commute 16,
    .commute 17, .commute 15, .braid 13, .braid 15, .braid 17, .commute 19, .commute 20,
    .commute 21, .commute 22])
,
  ([2, 4, 5, 0, 1, 8, 0, 5, 6, 2, 1, 0, 8, 0, 5, 1, 0, 2, 1, 8, 0, 6, 5, 2, 0, 8, 3, 2, 1, 0, 5,
    3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [2, 4, 5, 1, 0, 1, 8, 5, 0,
    1, 2, 6, 5, 0, 1, 0, 5, 6, 8, 0, 5, 1, 0, 8, 3, 2, 1, 0, 5, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 3, 2, 1, 0, 5, 6], [.commute 23, .commute 24, .braid 25, .commute 27, .commute 28,
    .commute 29, .square 30, .commute 18, .commute 16, .braid 11, .commute 13, .commute 14,
    .commute 15, .braid 16, .braid 18, .commute 20, .commute 21, .commute 19, .commute 13,
    .commute 14, .commute 10, .braid 11, .commute 13, .braid 14, .commute 16, .commute 17,
    .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 7, .commute 8,
    .commute 6, .commute 5, .braid 6, .braid 8, .commute 10, .commute 11, .braid 12, .commute
    14, .commute 15, .commute 16, .braid 17, .braid 19, .braid 21, .commute 23, .commute 24,
    .braid 25, .commute 27, .commute 28, .square 29, .commute 15, .commute 16, .commute 17,
    .commute 5, .commute 6, .commute 7, .commute 8, .braid 9, .commute 11, .commute 12, .braid
    13, .braid 3])
,
  ([2, 4, 5, 1, 0, 1, 8, 5, 0, 1, 2, 6, 5, 0, 1, 0, 5, 6, 8, 0, 5, 1, 0, 8, 3, 2, 1, 0, 5, 1, 0,
    8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [2, 4, 5, 1, 0, 8, 5, 0, 6, 1, 5, 2, 1,
    0, 5, 6, 8, 0, 5, 3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8, 2, 3, 2, 1, 0, 5, 6], [.commute 5,
    .commute 6, .braid 7, .commute 9, .commute 10, .braid 11, .commute 13, .braid 14, .commute
    16, .braid 17, .commute 19, .commute 20, .braid 21, .commute 23, .commute 24, .braid 25,
    .commute 27, .square 28, .commute 19, .braid 12, .commute 14, .commute 15, .commute 16,
    .braid 17, .braid 19, .commute 21, .commute 22, .commute 23, .commute 24, .braid 25, .square
    27, .commute 26, .commute 21, .commute 22, .commute 23, .braid 24, .braid 26, .square 28,
    .commute 27, .commute 20, .commute 21, .braid 22, .commute 24, .commute 25, .commute 26,
    .braid 27, .square 29, .commute 28, .commute 18, .commute 19, .braid 20, .commute 22,
    .commute 23, .commute 24, .commute 25, .commute 26, .commute 27, .braid 28, .square 30,
    .commute 29, .commute 30, .commute 9, .commute 10, .commute 8])
,
  ([2, 4, 5, 1, 0, 8, 5, 0, 6, 1, 5, 2, 1, 0, 5, 6, 8, 0, 5, 3, 2, 1, 0, 8, 5, 6, 0, 5, 1, 0, 8,
    2, 3, 2, 1, 0, 5, 6], [2, 4, 5, 1, 0, 8, 5, 0, 6, 5, 2, 1, 0, 5, 8, 3, 2, 1, 0, 5, 6, 8, 5,
    0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 0, 1], [.commute 9, .braid 10, .commute 12, .commute 13,
    .commute 14, .commute 15, .commute 16, .commute 17, .braid 18, .commute 20, .commute 21,
    .commute 22, .commute 23, .commute 24, .commute 25, .commute 26, .commute 27, .commute 28,
    .commute 29, .braid 30, .square 32, .commute 22, .commute 23, .commute 17, .commute 18,
    .commute 19, .braid 20, .commute 22, .braid 23, .commute 25, .commute 26, .braid 27,
    .commute 29, .commute 30, .braid 31, .commute 33, .commute 34, .commute 25, .commute 16,
    .commute 17, .braid 18, .commute 20, .commute 21, .commute 22, .braid 23, .braid 25,
    .commute 27, .commute 28, .commute 29, .commute 30, .braid 31, .commute 33, .commute 29,
    .commute 30, .commute 31, .commute 32, .commute 24, .commute 14, .commute 15, .commute 16,
    .commute 17, .commute 18, .braid 19, .commute 21])
,
  ([2, 4, 5, 1, 0, 8, 5, 0, 6, 5, 2, 1, 0, 5, 8, 3, 2, 1, 0, 5, 6, 8, 5, 0, 5, 1, 0, 8, 2, 1, 0,
    5, 6, 3, 0, 1], [2, 4, 1, 0, 5, 8, 0, 6, 5, 2, 1, 3, 2, 1, 0, 1, 8, 5, 0, 1, 6, 5, 0, 8, 2,
    1, 0, 5, 6, 5, 0, 1, 2, 3, 0, 1], [.braid 22, .braid 24, .commute 26, .braid 27, .commute
    29, .commute 30, .commute 31, .commute 13, .commute 14, .commute 15, .commute 16, .braid 17,
    .commute 19, .braid 20, .commute 22, .commute 23, .braid 24, .commute 26, .braid 27,
    .commute 29, .commute 30, .commute 22, .commute 5, .commute 2, .braid 3, .braid 5, .commute
    7, .commute 8, .commute 9, .commute 10, .braid 11, .commute 13, .commute 14, .braid 15,
    .commute 17, .commute 18, .commute 19, .braid 20, .braid 22, .commute 24, .commute 25,
    .commute 26, .braid 27, .commute 29, .commute 18, .commute 19, .commute 20, .commute 17,
    .commute 12, .commute 13, .commute 14, .braid 15, .braid 17, .commute 19, .braid 20,
    .commute 22, .commute 23, .commute 24, .commute 25, .commute 26, .braid 27, .commute 11,
    .commute 12, .braid 13])
,
  ([2, 4, 1, 0, 5, 8, 0, 6, 5, 2, 1, 3, 2, 1, 0, 1, 8, 5, 0, 1, 6, 5, 0, 8, 2, 1, 0, 5, 6, 5, 0,
    1, 2, 3, 0, 1], [2, 4, 1, 0, 5, 8, 3, 2, 1, 0, 1, 8, 5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5,
    6, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1], [.commute 15, .commute 16, .braid 17, .commute 19, .braid
    20, .commute 22, .commute 23, .commute 24, .braid 25, .commute 27, .commute 15, .commute 8,
    .commute 9, .commute 10, .commute 11, .commute 12, .braid 13, .braid 15, .commute 17,
    .commute 18, .commute 19, .braid 20, .commute 22, .braid 23, .commute 25, .commute 26,
    .commute 17, .commute 18, .commute 16, .commute 14, .commute 7, .commute 8, .commute 9,
    .commute 10, .commute 11, .commute 12, .commute 13, .braid 14, .braid 16, .braid 18,
    .commute 20, .braid 21, .commute 23, .commute 24, .commute 25, .commute 8, .braid 9,
    .commute 11, .commute 12, .commute 13, .commute 14, .commute 15, .commute 16, .braid 7,
    .commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .commute 14, .commute 15,
    .commute 6, .commute 7, .braid 8])
,
  ([2, 4, 1, 0, 5, 8, 3, 2, 1, 0, 1, 8, 5, 6, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0,
    1, 2, 3, 0, 1], [2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5,
    6, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1], [.commute 10, .commute 11, .commute 12, .commute 5,
    .commute 6, .commute 7, .braid 8, .commute 1, .commute 2, .commute 3])
,
  ([2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0,
    1, 2, 3, 0, 1, 1, 0, 8, 0, 1], [2, 1, 0, 4, 3, 2, 1, 3, 0, 5, 0, 8, 0, 1, 2, 6, 5, 0, 8, 1,
    0, 5, 6, 0, 5, 2, 1, 0, 8, 1, 0, 5, 1, 2, 3, 0, 1], [.square 35, .square 34, .commute 33,
    .commute 32, .commute 31, .braid 28, .commute 30, .commute 20, .commute 21, .commute 19,
    .braid 17, .braid 19, .braid 21, .commute 23, .commute 24, .commute 25, .commute 26,
    .commute 27, .braid 28, .commute 26, .commute 15, .commute 16, .commute 17, .commute 14,
    .commute 13, .braid 14, .commute 16, .braid 17, .commute 19, .commute 20, .braid 21,
    .commute 23, .commute 24, .commute 12, .commute 13, .commute 14, .commute 15, .commute 11,
    .commute 10, .braid 11, .commute 13, .commute 14, .braid 15, .commute 17, .commute 18,
    .commute 19, .commute 20, .braid 21, .commute 23, .braid 24, .braid 26, .commute 28,
    .commute 23, .commute 24, .commute 18, .commute 9, .commute 10, .commute 8, .commute 3,
    .commute 4, .commute 5, .commute 6, .commute 7, .braid 8])
,
  ([2, 1, 0, 4, 3, 2, 1, 3, 0, 5, 0, 8, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5, 6, 0, 5, 2, 1, 0, 8, 1, 0,
    5, 1, 2, 3, 0, 1], [2, 1, 4, 3, 2, 3, 1, 0, 5, 8, 0, 1, 6, 8, 0, 5, 0, 6, 1, 2, 8, 0, 1, 5,
    0, 8, 5, 6, 2, 1, 0, 5, 1, 2, 3, 0, 1], [.braid 10, .commute 12, .commute 13, .commute 14,
    .commute 15, .braid 16, .braid 18, .commute 20, .commute 21, .commute 6, .commute 2,
    .commute 3, .commute 4, .commute 5, .braid 6, .commute 8, .commute 9, .braid 10, .commute
    12, .commute 13, .braid 14, .commute 16, .commute 17, .braid 18, .commute 20, .braid 21,
    .commute 23, .braid 24, .commute 26, .commute 27, .commute 20, .commute 21, .commute 19,
    .braid 17, .braid 19, .braid 21, .commute 23, .commute 24, .commute 25, .commute 26,
    .commute 22, .commute 23, .commute 20, .commute 21, .commute 18, .commute 19, .commute 12,
    .commute 13, .commute 14, .commute 15, .commute 16, .commute 17, .commute 18, .braid 19,
    .braid 21, .braid 23, .commute 25, .braid 14, .commute 16, .commute 17, .commute 18,
    .commute 19, .commute 13, .braid 14])
,
  ([2, 1, 4, 3, 2, 3, 1, 0, 5, 8, 0, 1, 6, 8, 0, 5, 0, 6, 1, 2, 8, 0, 1, 5, 0, 8, 5, 6, 2, 1, 0,
    5, 1, 2, 3, 0, 1], [2, 1, 4, 3, 2, 5, 0, 1, 8, 0, 6, 5, 6, 0, 8, 1, 0, 5, 3, 2, 1, 0, 8, 2,
    1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 3, 0, 1], [.commute 16, .commute 11, .commute 12, .commute 10,
    .commute 9, .braid 10, .braid 12, .commute 14, .commute 15, .braid 16, .commute 18, .braid
    19, .commute 21, .commute 22, .braid 23, .commute 21, .commute 9, .commute 10, .commute 11,
    .commute 12, .braid 13, .braid 7, .commute 9, .commute 10, .braid 11, .commute 13, .braid
    14, .commute 16, .commute 17, .commute 18, .braid 19, .braid 21, .commute 23, .commute 17,
    .commute 18, .commute 19, .commute 16, .commute 9, .commute 6, .braid 7, .braid 9, .commute
    11, .commute 12, .commute 13, .braid 14, .braid 16, .commute 18, .braid 19, .commute 21,
    .commute 22, .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10,
    .commute 11, .commute 12, .commute 13, .commute 14, .commute 15, .commute 16, .commute 17,
    .braid 10])
,
  ([2, 1, 4, 3, 2, 5, 0, 1, 8, 0, 6, 5, 6, 0, 8, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0,
    5, 1, 2, 3, 0, 1], [5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 2,
    1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 3, 0, 1], [.commute 12, .commute 13, .commute 9, .braid 10,
    .commute 12, .commute 8, .commute 9, .braid 10, .commute 7, .commute 8, .commute 4, .commute
    5, .commute 6, .commute 7, .commute 3, .commute 4, .commute 5, .commute 6, .commute 2,
    .commute 3, .commute 4, .commute 5, .commute 3, .commute 1, .commute 2, .commute 0, .commute
    1])
,
  ([5, 6, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0,
    5, 1, 2, 3, 0, 1, 1, 0, 8, 0, 1], [5, 2, 1, 0, 4, 3, 2, 1, 8, 0, 5, 6, 3, 8, 0, 5, 1, 0, 1,
    8, 2, 1, 0, 5, 6, 1, 2, 0, 1, 8, 0, 5, 1, 2, 3, 8, 0, 1], [.square 36, .square 35, .commute
    22, .commute 23, .commute 21, .braid 19, .braid 21, .braid 23, .commute 25, .commute 26,
    .commute 27, .commute 28, .commute 17, .commute 18, .commute 19, .commute 16, .commute 15,
    .braid 16, .commute 18, .braid 19, .commute 21, .commute 22, .braid 23, .commute 25,
    .commute 26, .commute 21, .braid 10, .commute 12, .commute 13, .commute 14, .commute 5,
    .commute 6, .commute 7, .commute 8, .commute 9, .braid 10, .commute 12, .commute 13, .braid
    14, .commute 16, .commute 17, .commute 18, .braid 19, .braid 21, .commute 23, .commute 24,
    .commute 17, .commute 18, .commute 19, .commute 16, .commute 1, .commute 2, .commute 3,
    .commute 4, .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .braid 10, .commute
    12, .commute 13, .braid 14, .braid 16])
,
  ([5, 2, 1, 0, 4, 3, 2, 1, 8, 0, 5, 6, 3, 8, 0, 5, 1, 0, 1, 8, 2, 1, 0, 5, 6, 1, 2, 0, 1, 8, 0,
    5, 1, 2, 3, 8, 0, 1], [2, 1, 4, 3, 2, 3, 1, 0, 5, 6, 8, 0, 1, 5, 8, 0, 8, 2, 1, 0, 5, 6, 0,
    1, 2, 5, 0, 1, 8, 0, 5, 1, 2, 3, 0, 1], [.commute 18, .braid 19, .commute 21, .commute 22,
    .commute 23, .braid 24, .braid 26, .braid 28, .commute 30, .commute 31, .commute 32,
    .commute 33, .square 34, .commute 11, .commute 12, .commute 13, .commute 10, .commute 11,
    .commute 9, .commute 8, .braid 9, .braid 11, .braid 13, .commute 15, .commute 16, .commute
    17, .commute 18, .commute 19, .commute 20, .braid 21, .commute 23, .commute 24, .commute 14,
    .commute 12, .commute 7, .commute 3, .commute 4, .commute 5, .commute 6, .braid 7, .commute
    9, .commute 10, .commute 11, .braid 12, .braid 14, .commute 16, .commute 17, .commute 18,
    .braid 19, .commute 21, .commute 9, .commute 10, .commute 0, .commute 1, .commute 2,
    .commute 3, .commute 4, .commute 5, .commute 6, .braid 7, .commute 9, .braid 10, .commute
    12, .commute 13])
,
  ([2, 1, 4, 3, 2, 3, 1, 0, 5, 6, 8, 0, 1, 5, 8, 0, 8, 2, 1, 0, 5, 6, 0, 1, 2, 5, 0, 1, 8, 0, 5,
    1, 2, 3, 0, 1], [2, 1, 4, 3, 2, 3, 1, 0, 1, 5, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1], [.braid 14, .commute 16, .braid 17, .commute 19, .commute
    20, .braid 21, .commute 23, .braid 24, .commute 26, .commute 27, .braid 28, .commute 26,
    .commute 23, .commute 24, .commute 25, .commute 20, .commute 21, .braid 18, .commute 20,
    .braid 21, .commute 23, .commute 24, .commute 17, .braid 18, .commute 20, .braid 21,
    .commute 23, .commute 15, .commute 16, .commute 14, .commute 13, .braid 14, .braid 16,
    .commute 18, .commute 19, .commute 20, .braid 21, .commute 18, .commute 19, .commute 17,
    .commute 15, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .commute 14,
    .braid 15, .braid 17, .braid 19, .commute 21, .commute 12, .commute 13, .commute 14,
    .commute 15, .commute 16, .commute 17, .braid 10, .commute 12, .commute 13, .commute 14,
    .commute 9, .braid 10, .commute 8])
,
  ([2, 1, 4, 3, 2, 3, 1, 0, 1, 5, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0,
    1, 2, 3, 0, 1], [2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5,
    6, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1], [.braid 6, .braid 8, .commute 10, .braid 11, .commute 13,
    .braid 14, .commute 16, .braid 17, .commute 19, .commute 20, .commute 5, .commute 6,
    .commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13,
    .commute 14, .commute 15, .commute 6, .commute 4, .commute 5, .commute 3, .commute 4,
    .commute 2, .commute 3])
,
  ([2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 0,
    1, 2, 3, 0, 1, 6], [2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1], [.commute 25, .commute 26, .commute 27, .commute 24,
    .commute 25, .commute 23, .braid 21, .braid 23, .braid 25, .braid 27, .commute 29, .commute
    30, .commute 31, .commute 32, .commute 33, .commute 34, .square 35, .commute 26, .commute
    24, .commute 25, .commute 22, .commute 23, .commute 24])
,
  ([2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1,
    2, 3, 0, 1, 4], [2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6,
    2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1], [.commute 34, .commute 33])
,
  ([2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1,
    2, 3, 4, 0, 1, 1, 2, 1], [2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 2, 1, 0, 5, 0, 1, 2, 3, 4, 2, 0, 1], [.square 35, .commute 34])
,
  ([2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 0, 1,
    2, 3, 4, 2, 0, 1, 6, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 3, 2, 1, 0, 5, 6], [2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 1, 3, 2, 6, 5, 6, 0, 1, 2, 5, 6,
    0, 5, 8, 0, 1, 2, 3, 4, 2, 6, 0, 5, 6, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6,
    1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [.braid 27, .commute 29, .commute 30, .commute 31,
    .commute 32, .commute 33, .commute 26, .braid 27, .commute 29, .commute 30, .commute 31,
    .commute 32, .braid 33, .commute 35, .commute 24, .commute 23, .braid 24, .commute 26,
    .commute 27, .commute 28, .commute 29, .commute 30, .commute 31, .commute 22, .commute 23,
    .braid 24, .commute 26, .commute 27, .commute 28, .commute 29, .commute 30, .braid 31,
    .commute 33, .commute 34, .braid 35, .square 37, .commute 34, .commute 35, .braid 32,
    .commute 34, .braid 35, .commute 37, .square 38, .commute 20, .commute 21, .commute 22,
    .commute 23, .braid 18, .commute 20, .commute 21, .commute 15, .commute 16, .commute 14,
    .commute 15, .braid 16, .commute 18, .commute 19, .commute 12, .commute 13, .commute 14,
    .commute 11, .commute 12, .commute 13, .braid 14])
,
  ([2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 1, 3, 2, 6, 5, 6, 0, 1, 2, 5, 6, 0, 5, 8, 0, 1, 2, 3, 4, 2,
    6, 0, 5, 6, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2,
    1, 0, 5, 6], [2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3, 6, 5, 1, 0, 5, 6, 2, 1, 0, 5, 8, 0, 1, 2, 3,
    4, 1, 6, 8, 0, 5, 6, 2, 1, 0, 8, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0,
    8, 3, 2, 1, 0, 5, 6], [.commute 16, .commute 17, .commute 18, .braid 19, .braid 21, .braid
    23, .commute 25, .commute 26, .commute 27, .commute 28, .commute 29, .commute 30, .commute
    13, .commute 14, .commute 15, .braid 16, .commute 18, .commute 19, .commute 11, .commute 12,
    .commute 13, .braid 14, .commute 16, .commute 10, .commute 11, .braid 12, .commute 14,
    .commute 15, .braid 16, .commute 18, .braid 19, .commute 21, .commute 22, .braid 23,
    .commute 25, .commute 26, .commute 27, .commute 28, .commute 29, .braid 30, .commute 32,
    .commute 33, .commute 34, .braid 35, .square 37, .commute 28, .commute 29, .commute 30,
    .commute 31, .commute 32, .commute 15, .commute 16, .commute 17, .braid 13, .commute 15,
    .commute 16, .braid 17, .commute 19, .commute 20, .commute 21, .commute 22, .braid 23,
    .commute 25, .commute 26])
,
  ([2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 3, 6, 5, 1, 0, 5, 6, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 1, 6, 8, 0,
    5, 6, 2, 1, 0, 8, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0,
    5, 6], [2, 1, 0, 5, 4, 2, 3, 0, 8, 2, 1, 2, 0, 1, 5, 0, 8, 6, 5, 0, 1, 2, 3, 4, 5, 6, 0, 8,
    1, 0, 5, 6, 2, 1, 0, 8, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1,
    0, 5, 6], [.commute 27, .commute 28, .commute 12, .braid 13, .commute 15, .commute 16,
    .braid 17, .commute 19, .commute 20, .braid 21, .commute 23, .commute 24, .commute 25,
    .commute 26, .commute 11, .commute 12, .braid 13, .commute 15, .commute 16, .braid 17,
    .braid 19, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25, .braid 26,
    .braid 28, .commute 30, .commute 31, .braid 32, .commute 34, .commute 35, .commute 36,
    .commute 37, .square 38, .commute 18, .commute 9, .commute 10, .commute 8, .commute 7,
    .braid 8, .braid 10, .commute 12, .commute 13, .commute 14, .commute 15, .braid 16, .braid
    18, .commute 20, .commute 21, .commute 22, .commute 23, .commute 13, .commute 14, .commute
    15, .commute 16, .commute 12, .commute 13, .commute 11, .commute 9, .braid 5, .commute 7,
    .commute 8])
,
  ([2, 1, 0, 5, 4, 2, 3, 0, 8, 2, 1, 2, 0, 1, 5, 0, 8, 6, 5, 0, 1, 2, 3, 4, 5, 6, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 8, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5,
    6], [4, 1, 2, 3, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 6, 5, 0, 1, 2, 3, 4, 0, 5, 6, 5, 0, 8, 1, 0,
    5, 6, 2, 1, 0, 5, 8, 6, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5,
    6], [.braid 9, .braid 11, .braid 13, .commute 15, .braid 16, .commute 18, .commute 19,
    .commute 20, .commute 21, .commute 22, .braid 23, .commute 12, .commute 3, .commute 4,
    .commute 5, .commute 2, .commute 3, .commute 4, .braid 5, .commute 7, .commute 8, .commute
    9, .braid 10, .braid 12, .commute 14, .commute 15, .commute 16, .braid 17, .commute 19,
    .commute 20, .commute 21, .commute 7, .commute 8, .commute 1, .commute 0, .braid 1, .commute
    3, .commute 4, .braid 5, .commute 7, .braid 8, .commute 10, .commute 11, .braid 12, .commute
    14, .braid 15, .commute 17, .commute 18, .commute 19, .commute 20, .braid 21, .commute 23,
    .braid 24, .commute 26, .commute 27, .braid 28, .commute 30, .commute 31, .braid 32,
    .commute 34, .commute 35, .commute 36, .square 37, .commute 34])
,
  ([4, 1, 2, 3, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 6, 5, 0, 1, 2, 3, 4, 0, 5, 6, 5, 0, 8, 1, 0, 5, 6,
    2, 1, 0, 5, 8, 6, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [4,
    1, 2, 3, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 6, 5, 0, 1, 2, 3, 4, 6, 5, 0, 8, 1, 0, 5, 2, 1, 0, 1,
    5, 6, 8, 3, 2, 1, 0, 5, 6, 8, 1, 2, 0, 1, 5, 0, 8, 3, 2, 1, 0, 5, 6, 1], [.commute 35,
    .braid 22, .commute 24, .commute 25, .commute 26, .commute 27, .braid 28, .commute 30,
    .commute 31, .braid 32, .commute 34, .braid 35, .commute 37, .commute 38, .commute 39,
    .commute 40, .braid 41, .square 43, .commute 29, .commute 30, .commute 31, .braid 32,
    .commute 34, .braid 35, .commute 37, .commute 38, .braid 39, .commute 41, .commute 42,
    .commute 43, .square 44, .commute 41, .commute 42, .commute 36, .commute 37, .commute 38,
    .braid 39, .commute 41, .braid 42, .commute 44, .commute 45, .commute 46, .braid 47,
    .commute 49, .commute 50, .braid 51, .commute 53, .commute 54, .commute 44, .commute 45,
    .commute 43, .commute 35, .commute 36, .braid 37, .commute 39, .commute 40, .commute 41,
    .commute 21, .braid 22, .commute 24, .commute 25, .braid 26, .commute 28, .braid 29])
,
  ([4, 1, 2, 3, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 6, 5, 0, 1, 2, 3, 4, 6, 5, 0, 8, 1, 0, 5, 2, 1, 0,
    1, 5, 6, 8, 3, 2, 1, 0, 5, 6, 8, 1, 2, 0, 1, 5, 0, 8, 3, 2, 1, 0, 5, 6, 1], [4, 1, 2, 3, 5,
    0, 1, 2, 8, 0, 5, 1, 0, 8, 5, 6, 0, 5, 0, 1, 0, 8, 2, 1, 0, 5, 3, 2, 1, 0, 5, 8, 4, 3, 2, 1,
    0, 5, 6, 8, 1, 2, 0, 5, 1, 0, 8, 3, 2, 1, 0, 5, 6, 2, 0, 1], [.commute 31, .commute 32,
    .commute 33, .commute 34, .braid 35, .commute 37, .commute 38, .commute 39, .commute 40,
    .braid 41, .braid 43, .braid 45, .commute 47, .commute 48, .commute 49, .commute 50, .braid
    51, .commute 53, .commute 44, .commute 32, .commute 33, .commute 34, .commute 35, .commute
    36, .braid 37, .commute 39, .commute 40, .commute 41, .braid 42, .braid 44, .commute 46,
    .commute 47, .braid 48, .commute 50, .commute 51, .commute 52, .commute 20, .commute 21,
    .commute 22, .commute 23, .commute 24, .commute 25, .commute 26, .commute 27, .commute 28,
    .commute 29, .commute 30, .commute 31, .commute 19, .commute 20, .commute 21, .commute 22,
    .commute 23, .commute 24, .commute 25, .commute 18, .commute 19, .commute 20, .commute 21,
    .commute 17, .commute 18, .commute 16, .braid 14, .braid 16])
,
  ([4, 1, 2, 3, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 5, 6, 0, 5, 0, 1, 0, 8, 2, 1, 0, 5, 3, 2, 1, 0, 5,
    8, 4, 3, 2, 1, 0, 5, 6, 8, 1, 2, 0, 5, 1, 0, 8, 3, 2, 1, 0, 5, 6, 2, 0, 1], [4, 1, 2, 3, 5,
    0, 1, 2, 8, 1, 0, 5, 6, 8, 0, 1, 5, 0, 8, 2, 1, 0, 5, 3, 2, 1, 0, 5, 1, 8, 4, 3, 2, 1, 0, 5,
    6, 8, 1, 3, 2, 0, 5, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 2, 0, 1], [.braid 18, .commute 20, .braid
    21, .commute 23, .commute 24, .braid 25, .commute 27, .commute 28, .commute 29, .commute 30,
    .braid 31, .commute 33, .commute 34, .commute 35, .commute 36, .commute 37, .commute 38,
    .commute 39, .commute 40, .commute 41, .commute 42, .commute 43, .commute 44, .commute 45,
    .commute 13, .commute 14, .commute 10, .braid 11, .commute 13, .braid 14, .commute 16,
    .commute 17, .braid 18, .commute 20, .braid 21, .commute 23, .commute 24, .braid 25,
    .commute 27, .commute 28, .commute 29, .commute 30, .braid 31, .commute 33, .commute 34,
    .commute 35, .commute 36, .commute 37, .commute 38, .commute 16, .braid 9, .commute 11,
    .commute 12, .commute 13, .braid 14, .braid 16, .commute 18, .commute 19, .commute 20,
    .braid 21, .commute 23, .commute 24, .braid 25, .commute 27])
,
  ([4, 1, 2, 3, 5, 0, 1, 2, 8, 1, 0, 5, 6, 8, 0, 1, 5, 0, 8, 2, 1, 0, 5, 3, 2, 1, 0, 5, 1, 8, 4,
    3, 2, 1, 0, 5, 6, 8, 1, 3, 2, 0, 5, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 2, 0, 1], [4, 1, 5, 0, 8,
    3, 2, 1, 0, 5, 6, 8, 0, 5, 1, 0, 8, 2, 3, 1, 2, 0, 1, 8, 0, 5, 0, 8, 4, 3, 2, 1, 0, 1, 5, 6,
    8, 2, 1, 3, 2, 0, 5, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 2, 0, 1], [.commute 28, .commute 29,
    .commute 30, .braid 31, .commute 33, .commute 34, .commute 35, .commute 36, .commute 22,
    .commute 23, .commute 24, .braid 25, .commute 18, .commute 19, .commute 17, .commute 15,
    .commute 7, .commute 6, .braid 7, .commute 9, .commute 10, .commute 11, .commute 12,
    .commute 13, .commute 14, .braid 15, .braid 17, .braid 19, .commute 21, .commute 22,
    .commute 23, .commute 20, .commute 21, .commute 18, .commute 19, .commute 16, .commute 17,
    .commute 3, .commute 4, .commute 5, .commute 2, .commute 3, .commute 4, .braid 5, .commute
    7, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13, .commute 14,
    .commute 15, .commute 16, .braid 17, .braid 19, .braid 21, .braid 23, .commute 25, .braid
    26, .commute 28, .commute 29, .commute 30, .braid 31])
,
  ([4, 1, 5, 0, 8, 3, 2, 1, 0, 5, 6, 8, 0, 5, 1, 0, 8, 2, 3, 1, 2, 0, 1, 8, 0, 5, 0, 8, 4, 3, 2,
    1, 0, 1, 5, 6, 8, 2, 1, 3, 2, 0, 5, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 2, 0, 1], [4, 1, 5, 0, 8,
    3, 2, 1, 0, 5, 6, 8, 0, 5, 1, 0, 2, 3, 1, 2, 0, 8, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 2, 0, 1, 3,
    2, 5, 0, 6, 5, 1, 0, 8, 4, 3, 2, 1, 6, 0, 5, 6, 4, 2, 0, 1], [.commute 33, .commute 34,
    .commute 35, .braid 36, .braid 38, .commute 40, .commute 41, .commute 42, .commute 43,
    .commute 44, .braid 45, .commute 47, .commute 48, .commute 49, .commute 50, .commute 51,
    .commute 34, .commute 35, .commute 36, .commute 37, .commute 38, .commute 39, .commute 33,
    .commute 34, .commute 35, .commute 36, .commute 37, .commute 27, .commute 28, .commute 29,
    .commute 30, .braid 31, .commute 33, .commute 26, .commute 27, .commute 28, .braid 29,
    .commute 31, .commute 22, .commute 16, .commute 17, .commute 18, .commute 19, .braid 20,
    .braid 22, .commute 24, .commute 25, .commute 26, .braid 27, .commute 29, .commute 30,
    .braid 31, .braid 33, .commute 35, .commute 36, .braid 37, .braid 39, .commute 41, .commute
    42, .commute 43, .commute 44, .commute 45, .commute 46, .commute 47])
,
  ([4, 1, 5, 0, 8, 3, 2, 1, 0, 5, 6, 8, 0, 5, 1, 0, 2, 3, 1, 2, 0, 8, 1, 0, 5, 4, 3, 2, 1, 0, 8,
    1, 2, 0, 1, 3, 2, 5, 0, 6, 5, 1, 0, 8, 4, 3, 2, 1, 6, 0, 5, 6, 4, 2, 0, 1], [4, 1, 5, 0, 8,
    3, 2, 1, 0, 5, 6, 8, 0, 5, 1, 2, 3, 1, 0, 2, 1, 8, 4, 3, 5, 0, 8, 1, 2, 3, 5, 0, 1, 2, 0, 5,
    6, 8, 0, 1, 5, 0, 8, 4, 3, 2, 1, 0, 5, 6, 0, 5, 4, 2, 0, 1], [.commute 48, .braid 49,
    .commute 40, .commute 38, .commute 34, .commute 32, .commute 19, .commute 20, .commute 15,
    .commute 16, .braid 17, .commute 19, .braid 20, .commute 22, .commute 23, .commute 24,
    .braid 25, .commute 27, .commute 28, .commute 29, .commute 30, .commute 31, .braid 32,
    .braid 34, .commute 36, .commute 37, .braid 38, .braid 40, .commute 42, .commute 43,
    .commute 44, .commute 45, .commute 46, .braid 47, .commute 49, .commute 29, .braid 27,
    .braid 29, .commute 31, .commute 32, .commute 33, .commute 34, .commute 35, .commute 36,
    .commute 30, .commute 31, .commute 28, .commute 26, .commute 27, .braid 28, .commute 30,
    .braid 31, .commute 33, .commute 23, .commute 24, .commute 22, .commute 23, .braid 24,
    .commute 26, .commute 27, .commute 28, .commute 29, .commute 19, .commute 20])
,
  ([4, 1, 5, 0, 8, 3, 2, 1, 0, 5, 6, 8, 0, 5, 1, 2, 3, 1, 0, 2, 1, 8, 4, 3, 5, 0, 8, 1, 2, 3, 5,
    0, 1, 2, 0, 5, 6, 8, 0, 1, 5, 0, 8, 4, 3, 2, 1, 0, 5, 6, 0, 5, 4, 2, 0, 1], [4, 1, 5, 0, 8,
    3, 2, 1, 0, 5, 6, 8, 0, 2, 1, 3, 2, 4, 3, 0, 5, 1, 0, 8, 0, 4, 1, 2, 5, 0, 1, 0, 5, 6, 8, 0,
    5, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 4, 2, 0, 1], [.commute 21, .commute 22,
    .commute 23, .braid 24, .commute 20, .commute 21, .commute 22, .commute 18, .commute 19,
    .commute 20, .commute 13, .commute 14, .commute 15, .commute 16, .commute 17, .commute 18,
    .commute 19, .braid 20, .braid 22, .commute 24, .braid 25, .commute 27, .commute 28, .braid
    29, .commute 31, .commute 32, .braid 33, .commute 35, .braid 36, .commute 38, .commute 39,
    .braid 40, .commute 42, .commute 43, .commute 44, .braid 45, .commute 47, .commute 48,
    .commute 38, .commute 32, .commute 33, .commute 34, .commute 35, .commute 36, .commute 37,
    .commute 28, .commute 29, .commute 30, .commute 31, .commute 32, .commute 33, .commute 34,
    .commute 35, .commute 36, .commute 15, .braid 13, .braid 15, .braid 17, .commute 19,
    .commute 20, .commute 21, .commute 22, .commute 23, .commute 24])
,
  ([4, 1, 5, 0, 8, 3, 2, 1, 0, 5, 6, 8, 0, 2, 1, 3, 2, 4, 3, 0, 5, 1, 0, 8, 0, 4, 1, 2, 5, 0, 1,
    0, 5, 6, 8, 0, 5, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 4, 2, 0, 1], [4, 1, 5, 0, 8,
    3, 2, 1, 0, 5, 6, 8, 2, 3, 4, 1, 0, 2, 1, 8, 0, 5, 3, 2, 0, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5,
    4, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 4, 2, 0, 1], [.commute 25, .commute 26,
    .commute 27, .commute 28, .commute 29, .commute 30, .commute 31, .commute 32, .commute 33,
    .commute 34, .commute 35, .braid 28, .commute 30, .commute 31, .commute 32, .commute 26,
    .commute 25, .braid 26, .commute 28, .commute 29, .commute 30, .commute 31, .commute 18,
    .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .commute 16,
    .commute 17, .commute 18, .commute 14, .commute 15, .commute 12, .commute 13, .commute 14,
    .braid 15, .commute 17, .braid 18, .commute 20, .commute 21, .commute 22, .commute 23,
    .braid 24, .commute 26, .commute 27, .commute 28, .commute 29, .commute 30, .commute 29,
    .commute 28, .braid 20, .commute 22, .commute 23, .commute 24, .commute 25, .braid 26,
    .commute 17, .commute 18, .commute 19, .braid 20, .commute 22, .commute 23])
,
  ([4, 1, 5, 0, 8, 3, 2, 1, 0, 5, 6, 8, 2, 3, 4, 1, 0, 2, 1, 8, 0, 5, 3, 2, 0, 1, 0, 8, 0, 5, 6,
    3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 4, 2, 0, 1], [5, 0, 1, 8, 4,
    0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5,
    4, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 4, 2, 0, 1], [.braid 24, .commute 26,
    .commute 18, .commute 16, .commute 11, .commute 12, .commute 13, .commute 14, .commute 15,
    .braid 16, .braid 18, .commute 20, .commute 21, .braid 22, .commute 24, .commute 25,
    .commute 13, .commute 14, .commute 15, .commute 16, .commute 17, .commute 18, .commute 19,
    .commute 14, .commute 15, .commute 12, .commute 13, .commute 14, .commute 10, .commute 11,
    .commute 12, .commute 13, .commute 9, .commute 10, .commute 8, .braid 6, .braid 8, .braid
    10, .commute 12, .commute 4, .commute 5, .commute 6, .commute 3, .commute 1, .commute 2,
    .braid 3, .commute 5, .braid 6, .commute 8, .commute 9, .braid 10, .commute 8, .commute 5,
    .commute 6, .commute 7, .commute 2, .commute 3, .commute 4, .commute 5, .commute 6, .commute
    0, .commute 1, .commute 2, .commute 3])
,
  ([5, 0, 1, 8, 4, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6,
    3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 4, 2, 0, 1], [5, 0, 8, 1, 0,
    5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5,
    4, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 4, 2, 0, 1], [.commute 4, .commute 5,
    .commute 2])
,
  ([5, 0, 8, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6,
    3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 4, 2, 0, 1, 5, 1, 0, 8, 0, 5,
    1], [5, 0, 8, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0,
    5, 2, 3, 4, 6, 1, 2, 3, 0, 1, 2, 5, 0, 1, 8, 0, 5, 6, 4, 1, 0, 5, 1, 2, 0, 1], [.commute 51,
    .commute 52, .commute 50, .commute 51, .braid 52, .commute 54, .square 55, .square 54,
    .square 53, .commute 41, .commute 42, .commute 43, .commute 44, .commute 40, .commute 41,
    .commute 42, .commute 39, .commute 40, .commute 38, .braid 36, .braid 38, .braid 40, .braid
    42, .braid 44, .commute 46, .commute 47, .commute 48, .commute 49, .commute 50, .commute 51,
    .square 52, .braid 51, .commute 50, .commute 51, .commute 48, .commute 35, .commute 36,
    .commute 37, .commute 38, .commute 39, .commute 40, .commute 34, .commute 35, .commute 36,
    .commute 37, .commute 33, .commute 34, .braid 31, .commute 33, .braid 34, .commute 36,
    .braid 37, .commute 39, .braid 40, .commute 42, .commute 43, .braid 44, .commute 46,
    .commute 47, .braid 48, .commute 50, .commute 30, .commute 31, .commute 32])
,
  ([5, 0, 8, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 2,
    3, 4, 6, 1, 2, 3, 0, 1, 2, 5, 0, 1, 8, 0, 5, 6, 4, 1, 0, 5, 1, 2, 0, 1], [5, 0, 8, 1, 0, 5,
    4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 2, 3, 0, 1, 5, 0, 6, 5, 2, 1,
    0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 4, 0, 1, 2, 0, 1], [.commute 33, .commute 34, .commute
    35, .commute 36, .commute 37, .commute 38, .commute 29, .commute 30, .commute 31, .commute
    32, .commute 33, .commute 34, .commute 28, .commute 29, .commute 30, .braid 26, .commute 28,
    .commute 29, .braid 30, .commute 32, .commute 33, .braid 34, .commute 36, .commute 37,
    .braid 38, .commute 40, .commute 41, .commute 42, .commute 43, .braid 44, .commute 46,
    .commute 47, .braid 48, .commute 46, .commute 47, .commute 48, .commute 41, .commute 37,
    .commute 38, .commute 39, .commute 40, .commute 33, .commute 34, .commute 35, .commute 36,
    .commute 37, .commute 38, .commute 39, .commute 29, .commute 30, .commute 31, .commute 32,
    .commute 33, .commute 34, .commute 35, .commute 36, .commute 37, .commute 38, .commute 34,
    .commute 35, .commute 31, .commute 32, .commute 33, .commute 34])
,
  ([5, 0, 8, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 2, 3, 0, 1,
    5, 0, 6, 5, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 4, 0, 1, 2, 0, 1], [5, 0, 8, 1, 0, 5,
    4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1,
    0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 4, 0, 1, 2, 0, 1], [.commute 28, .commute 29, .commute
    30, .commute 31, .commute 32, .commute 33, .commute 31, .commute 29, .commute 30, .commute
    27, .commute 28, .commute 29])
,
  ([5, 0, 8, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 4, 0, 1, 2, 0, 1, 3], [5, 0, 8, 1, 0,
    5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2,
    1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 4, 0, 1, 2, 3, 0, 1], [.commute 54, .commute 53])
,
  ([5, 0, 8, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 4, 0, 1, 2, 3, 0, 1, 4], [5, 0, 8, 1,
    0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 3, 0, 1], [.commute 55, .commute
    54, .commute 49, .commute 50, .commute 51, .braid 52])
,
  ([5, 0, 8, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 4, 3, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 3, 0, 1, 6], [5, 0, 8,
    1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5,
    3, 2, 1, 0, 8, 0, 5, 6, 4, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 3, 0, 1], [.commute 45, .commute
    46, .commute 44, .braid 42, .braid 44, .braid 46, .commute 48, .commute 49, .commute 50,
    .commute 51, .commute 52, .commute 53, .commute 54, .commute 55, .square 56, .commute 45,
    .commute 43, .commute 44, .commute 41, .commute 42, .commute 43, .commute 40, .commute 41,
    .commute 42, .commute 39, .commute 40, .commute 41])
,
  ([5, 0, 8, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 4, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 3, 0, 1, 6, 5, 0, 8, 1, 0,
    5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [5, 0, 8,
    1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5,
    3, 2, 1, 0, 8, 4, 3, 6, 5, 0, 1, 2, 3, 4, 3, 6, 0, 1, 5, 0, 5, 8, 0, 6, 5, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [.braid 46, .commute 48,
    .commute 49, .commute 50, .commute 51, .commute 52, .commute 45, .braid 46, .commute 48,
    .commute 49, .commute 50, .commute 51, .braid 52, .commute 54, .commute 41, .commute 42,
    .commute 43, .commute 40, .commute 41, .commute 42, .braid 43, .commute 45, .commute 46,
    .commute 47, .commute 48, .commute 49, .commute 50, .commute 39, .commute 40, .commute 41,
    .commute 42, .braid 43, .commute 45, .commute 46, .commute 47, .commute 48, .commute 49,
    .braid 50, .commute 52, .commute 53, .braid 54, .square 56, .commute 53, .commute 54, .braid
    51, .commute 53, .braid 54, .commute 56, .square 57, .commute 53, .commute 54, .commute 55,
    .commute 56, .commute 52, .commute 41, .commute 42, .commute 43, .braid 44, .commute 46,
    .commute 47, .commute 48, .commute 49, .braid 50, .braid 52])
,
  ([5, 0, 8, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 4, 3, 6, 5, 0, 1, 2, 3, 4, 3, 6, 0, 1, 5, 0, 5, 8, 0, 6, 5, 6, 2, 1,
    0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [5, 0, 8, 1, 0, 5, 4,
    3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 2, 1, 3, 2, 4, 3, 0, 5, 6, 1,
    0, 5, 8, 0, 1, 2, 3, 4, 3, 6, 8, 0, 1, 5, 0, 8, 5, 0, 6, 2, 1, 5, 0, 5, 3, 2, 1, 0, 8, 0, 5,
    6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [.commute 54, .commute 38, .commute 39, .commute
    40, .commute 41, .commute 37, .commute 38, .commute 39, .commute 33, .commute 34, .commute
    35, .commute 36, .commute 37, .commute 29, .commute 30, .commute 31, .commute 32, .commute
    33, .commute 34, .commute 35, .commute 36, .braid 37, .braid 39, .braid 41, .commute 43,
    .commute 44, .commute 45, .commute 46, .commute 47, .commute 48, .commute 34, .commute 35,
    .commute 36, .commute 37, .commute 31, .commute 32, .commute 33, .commute 34, .commute 28,
    .commute 29, .commute 30, .commute 31, .commute 32, .commute 33, .braid 34, .commute 36,
    .braid 37, .commute 39, .commute 40, .braid 41, .commute 43, .commute 44, .commute 45,
    .commute 46, .commute 47, .braid 48, .commute 50, .commute 51, .braid 52, .braid 54, .braid
    56, .square 58, .commute 57, .commute 58])
,
  ([5, 0, 8, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 1, 0, 2, 1, 3,
    2, 4, 3, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 3, 4, 3, 6, 8, 0, 1, 5, 0, 8, 5, 0, 6, 2, 1, 5, 0, 5,
    3, 2, 1, 0, 8, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [5, 0, 8, 1, 0, 5, 4, 3, 2,
    1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 2, 0, 5, 6, 3, 2, 1, 0, 5, 8, 0, 1,
    2, 3, 4, 1, 2, 3, 6, 8, 2, 1, 0, 5, 8, 6, 1, 2, 0, 1, 8, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 1,
    0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [.braid 59, .commute 61, .commute 62, .braid 63,
    .commute 65, .commute 53, .braid 51, .braid 53, .commute 55, .commute 56, .commute 57,
    .commute 54, .commute 55, .braid 49, .commute 51, .commute 52, .commute 53, .commute 33,
    .commute 34, .commute 35, .commute 36, .commute 37, .commute 38, .commute 39, .commute 40,
    .commute 41, .braid 42, .commute 44, .commute 32, .commute 33, .commute 34, .commute 35,
    .commute 36, .commute 37, .commute 38, .commute 39, .commute 40, .commute 41, .braid 42,
    .braid 44, .commute 46, .commute 47, .commute 31, .commute 32, .commute 33, .commute 29,
    .commute 27, .commute 28, .braid 29, .commute 31, .commute 32, .braid 33, .commute 35,
    .commute 36, .commute 37, .commute 38, .braid 39, .commute 41, .commute 42, .commute 28,
    .commute 29, .commute 30, .commute 31, .braid 26])
,
  ([5, 0, 8, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 2, 0, 5,
    6, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 1, 2, 3, 6, 8, 2, 1, 0, 5, 8, 6, 1, 2, 0, 1, 8, 0, 5, 3,
    2, 1, 0, 8, 1, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [5, 0, 8, 1, 0, 5, 4, 3, 2,
    1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 8, 0, 1, 2,
    3, 4, 1, 6, 8, 3, 2, 1, 0, 5, 8, 6, 1, 0, 8, 2, 3, 1, 2, 0, 1, 5, 0, 8, 1, 0, 5, 6, 5, 2, 1,
    0, 8, 3, 2, 1, 0, 5, 6], [.commute 28, .commute 29, .commute 30, .braid 31, .commute 33,
    .commute 34, .commute 35, .commute 36, .commute 37, .commute 38, .braid 39, .commute 41,
    .braid 42, .commute 44, .commute 45, .commute 46, .braid 47, .commute 49, .commute 50,
    .commute 51, .commute 52, .braid 53, .braid 55, .braid 57, .commute 59, .commute 60,
    .commute 61, .commute 62, .braid 63, .braid 65, .commute 67, .commute 68, .square 69,
    .commute 59, .commute 60, .commute 61, .commute 58, .commute 59, .commute 56, .commute 57,
    .commute 54, .commute 55, .commute 44, .commute 45, .commute 43, .commute 44, .braid 45,
    .commute 47, .commute 48, .commute 49, .commute 50, .commute 51, .commute 52, .commute 53,
    .commute 54, .braid 55, .braid 57, .braid 59, .braid 61, .commute 63, .commute 64, .braid
    65, .commute 67, .square 68])
,
  ([5, 0, 8, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6,
    3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 1, 6, 8, 3, 2, 1, 0, 5, 8, 6, 1, 0, 8, 2, 3, 1, 2, 0, 1, 5,
    0, 8, 1, 0, 5, 6, 5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6], [5, 0, 8, 1, 0, 5, 4, 3, 2, 1, 0, 8, 0,
    5, 6, 3, 2, 1, 0, 5, 4, 3, 1, 2, 0, 1, 8, 0, 5, 6, 3, 2, 1, 0, 8, 5, 0, 5, 1, 2, 3, 4, 8, 3,
    2, 1, 0, 5, 6, 1, 2, 3, 5, 0, 8, 1, 2, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 5, 1, 2, 1, 0, 8, 3, 2,
    1, 0, 5, 6], [.commute 54, .commute 55, .commute 56, .commute 57, .commute 53, .commute 54,
    .commute 42, .commute 43, .commute 44, .braid 45, .commute 47, .commute 48, .commute 49,
    .commute 50, .braid 51, .commute 53, .braid 54, .commute 56, .braid 57, .commute 59,
    .commute 60, .braid 61, .braid 63, .commute 65, .commute 66, .commute 67, .commute 56,
    .commute 57, .commute 55, .commute 49, .commute 50, .commute 51, .commute 52, .braid 53,
    .braid 55, .braid 57, .commute 59, .commute 60, .commute 61, .commute 58, .commute 56,
    .commute 42, .commute 43, .commute 44, .commute 45, .commute 46, .braid 47, .commute 49,
    .commute 50, .commute 51, .commute 35, .commute 25, .commute 26, .commute 24, .braid 22,
    .braid 24, .braid 26, .commute 28, .commute 29, .commute 30, .commute 31, .commute 32,
    .braid 33, .braid 35])
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
