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
/-- Exact bounded chunks of literal E8 square, commutation and braid moves, block 9. -/
def y431AuxE8RewriteData09 : Fin 64 → List (Fin 9) × List (Fin 9) × List Y431CoxeterMove :=
![
  ([0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 1, 2,
    3, 1, 2, 0, 1, 0, 5], [0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    1, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 2, 0, 1], [.braid 34, .commute 36, .commute 28, .commute
    29, .commute 30, .commute 31, .commute 32, .commute 33, .braid 34, .braid 31, .commute 33,
    .commute 34, .braid 29, .commute 31, .commute 32, .commute 33, .commute 28, .braid 29,
    .commute 31, .commute 32, .commute 27, .commute 28, .braid 29, .commute 31])
,
  ([0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0,
    5, 1, 2, 3, 2, 0, 1, 8], [0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 2, 1, 3, 2, 6, 5, 0, 1, 3, 8,
    2, 0, 8, 5, 0, 6, 5, 1, 0, 8, 1, 0, 5, 2, 3, 2, 1], [.commute 37, .commute 35, .commute 36,
    .commute 34, .commute 35, .commute 33, .commute 34, .commute 31, .braid 29, .braid 31,
    .commute 33, .commute 22, .braid 20, .braid 22, .commute 24, .commute 25, .commute 26,
    .commute 27, .commute 17, .commute 18, .commute 16, .commute 17, .braid 18, .commute 20,
    .commute 21, .braid 22, .commute 24, .commute 25, .commute 26, .braid 27, .commute 29,
    .commute 30, .braid 31, .commute 29, .commute 13, .commute 14, .commute 15, .commute 16,
    .commute 12, .commute 13, .commute 14, .commute 15, .braid 16, .commute 18, .commute 19,
    .commute 20, .commute 21, .braid 22, .commute 24, .commute 25, .commute 26, .braid 27,
    .braid 29, .commute 31, .commute 23, .commute 24, .commute 25, .commute 26, .commute 22,
    .commute 23, .commute 24, .commute 21, .commute 22, .commute 20])
,
  ([0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 2, 1, 3, 2, 6, 5, 0, 1, 3, 8, 2, 0, 8, 5, 0, 6, 5, 1, 0,
    8, 1, 0, 5, 2, 3, 2, 1], [0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 6, 5, 3, 2, 1, 0, 8, 5, 2, 6,
    1, 0, 5, 3, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 3, 2, 1], [.commute 21, .braid 22, .braid 24,
    .braid 26, .commute 28, .commute 29, .commute 30, .commute 27, .commute 25, .commute 19,
    .commute 15, .commute 16, .commute 17, .commute 14, .commute 15, .commute 16, .braid 17,
    .braid 19, .commute 16, .commute 17, .commute 13, .commute 14, .commute 12, .commute 13,
    .braid 14, .commute 16, .braid 17, .commute 19, .braid 20, .commute 22, .commute 23,
    .commute 24, .braid 25, .braid 27, .commute 29, .commute 26, .braid 18, .commute 20,
    .commute 21, .commute 22, .commute 23, .commute 24, .commute 25, .commute 16, .commute 15,
    .braid 16, .commute 18, .commute 19, .commute 20, .commute 21, .commute 22, .commute 23,
    .commute 24, .commute 15, .commute 16, .braid 17, .commute 19, .commute 20, .commute 21,
    .commute 14, .braid 15, .commute 17, .commute 18, .commute 19])
,
  ([0, 8, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 6, 5, 3, 2, 1, 0, 8, 5, 2, 6, 1, 0, 5, 3, 2, 1, 0, 8, 5,
    6, 1, 0, 5, 2, 3, 2, 1], [0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 3, 2, 1], [.commute 20, .braid 9, .commute 11,
    .commute 12, .commute 13, .commute 14, .commute 15, .braid 16, .commute 10, .commute 6,
    .commute 7, .commute 8, .commute 3, .commute 4, .commute 5, .commute 6, .commute 7, .braid
    8, .braid 10, .commute 12, .commute 13, .braid 14, .commute 16, .commute 6, .commute 7,
    .commute 8, .commute 5, .commute 6, .commute 7, .commute 1, .commute 2, .braid 3])
,
  ([0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 5,
    6, 1, 0, 5, 2, 3, 2, 1, 2], [0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 5, 6, 1, 0, 5, 2, 3, 1, 2, 1], [.braid 37])
,
  ([0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 5,
    6, 1, 0, 5, 2, 3, 1, 2, 1, 6], [0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 2, 3, 1, 2, 1], [.commute 39, .commute 38,
    .commute 37, .commute 36, .commute 35, .commute 31, .commute 32, .braid 33, .commute 30,
    .braid 31, .commute 33])
,
  ([0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 0, 5, 2, 3, 1, 2, 1, 3], [0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0,
    5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 1, 2, 3, 1, 2, 1], [.commute 40, .commute
    37, .braid 38, .braid 36, .commute 38])
,
  ([0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 0, 5, 1, 2, 3, 1, 2, 1, 0], [0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 1, 2, 3, 1, 2, 1, 0], [])
,
  ([0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 0, 5, 1, 2, 3, 1, 2, 1, 0, 1], [0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [.braid
    41])
,
  ([0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0, 5], [0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0,
    8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 2, 0, 1],
    [.braid 41, .commute 43, .commute 35, .commute 36, .commute 37, .commute 38, .commute 39,
    .commute 40, .braid 41, .braid 38, .commute 40, .commute 41, .braid 36, .commute 38,
    .commute 39, .commute 40, .commute 35, .braid 36, .commute 38, .commute 39, .commute 34,
    .commute 35, .braid 36, .commute 38])
,
  ([0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 2, 0, 1, 8], [0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 0,
    1, 8, 0, 2, 1, 3, 8, 2, 6, 5, 0, 8, 1, 0, 5, 6, 3, 8, 0, 5, 2, 1, 0, 8, 1, 0, 5, 2, 3, 2,
    1], [.commute 44, .commute 42, .commute 43, .commute 41, .commute 42, .commute 40, .commute
    41, .commute 38, .braid 36, .braid 38, .commute 40, .commute 29, .braid 27, .braid 29,
    .commute 31, .commute 32, .commute 33, .commute 34, .commute 24, .commute 25, .commute 23,
    .commute 24, .braid 25, .commute 27, .commute 28, .braid 29, .commute 31, .commute 32,
    .commute 33, .braid 34, .commute 36, .commute 37, .braid 38, .commute 36, .commute 20,
    .commute 21, .commute 22, .commute 23, .commute 19, .commute 20, .commute 21, .commute 22,
    .braid 23, .commute 25, .commute 26, .commute 27, .commute 28, .braid 29, .commute 31,
    .commute 32, .commute 33, .braid 34, .braid 36, .commute 38, .commute 32, .commute 33,
    .commute 34, .commute 26, .commute 16, .braid 14, .braid 16, .commute 18, .commute 19,
    .commute 20])
,
  ([0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 3, 2, 0, 1, 8, 0, 2, 1, 3, 8, 2, 6, 5, 0, 8, 1, 0, 5, 6,
    3, 8, 0, 5, 2, 1, 0, 8, 1, 0, 5, 2, 3, 2, 1], [0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 8, 1,
    0, 2, 3, 1, 2, 6, 3, 0, 5, 0, 1, 0, 8, 0, 1, 5, 0, 6, 5, 2, 1, 0, 8, 2, 1, 0, 5, 2, 3, 2,
    1], [.commute 21, .commute 22, .commute 23, .braid 24, .braid 26, .commute 28, .commute 29,
    .commute 30, .commute 31, .commute 17, .commute 15, .commute 13, .commute 14, .braid 15,
    .braid 17, .commute 19, .commute 20, .commute 21, .braid 22, .commute 24, .commute 25,
    .braid 26, .commute 28, .commute 29, .commute 24, .commute 18, .commute 16, .commute 12,
    .commute 13, .commute 14, .commute 15, .braid 16, .braid 18, .commute 20, .commute 21,
    .braid 22, .braid 24, .commute 26, .commute 27, .commute 28, .braid 29, .braid 31, .commute
    33, .braid 34, .commute 36, .commute 37, .commute 27, .commute 28, .commute 29, .commute 30,
    .commute 31, .commute 26, .commute 25, .braid 26, .commute 28, .commute 29, .commute 24,
    .commute 25, .braid 26, .commute 23, .commute 24, .commute 22, .commute 21, .braid 22])
,
  ([0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 0, 8, 1, 0, 2, 3, 1, 2, 6, 3, 0, 5, 0, 1, 0, 8, 0, 1, 5,
    0, 6, 5, 2, 1, 0, 8, 2, 1, 0, 5, 2, 3, 2, 1], [0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 6, 8, 0,
    1, 2, 3, 1, 2, 0, 8, 1, 0, 1, 5, 6, 0, 1, 2, 8, 0, 1, 5, 0, 8, 5, 6, 2, 1, 0, 5, 2, 3, 2,
    1], [.braid 24, .commute 26, .braid 27, .braid 29, .braid 31, .commute 33, .commute 34,
    .commute 35, .commute 36, .commute 32, .commute 33, .commute 30, .commute 31, .commute 28,
    .commute 29, .commute 19, .commute 17, .commute 18, .braid 19, .commute 21, .commute 22,
    .commute 17, .commute 16, .braid 17, .commute 19, .commute 15, .commute 14, .braid 15,
    .commute 17, .commute 18, .braid 19, .commute 21, .braid 22, .commute 24, .commute 25,
    .commute 26, .commute 27, .commute 28, .braid 29, .braid 31, .braid 33, .commute 35, .braid
    24, .commute 26, .commute 27, .commute 28, .commute 29, .commute 21, .commute 22, .commute
    23, .braid 24, .commute 26, .commute 22, .commute 20, .commute 13, .commute 12, .braid 13,
    .commute 15, .commute 16, .commute 17, .commute 18, .commute 19, .braid 20, .braid 22])
,
  ([0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 6, 8, 0, 1, 2, 3, 1, 2, 0, 8, 1, 0, 1, 5, 6, 0, 1, 2, 8,
    0, 1, 5, 0, 8, 5, 6, 2, 1, 0, 5, 2, 3, 2, 1], [0, 5, 1, 0, 8, 0, 5, 2, 1, 0, 5, 6, 8, 2, 3,
    1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2, 3, 2,
    1], [.commute 24, .commute 25, .braid 26, .commute 28, .braid 29, .commute 31, .commute 32,
    .braid 33, .commute 31, .commute 28, .commute 29, .commute 30, .commute 17, .braid 15,
    .braid 17, .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute 24,
    .commute 25, .commute 26, .commute 27, .commute 28, .commute 29, .commute 26, .commute 18,
    .commute 19, .commute 16, .commute 14, .commute 15, .braid 16, .commute 18, .braid 19,
    .commute 21, .commute 22, .commute 23, .commute 24, .commute 25, .commute 23, .commute 24,
    .braid 21, .commute 23, .commute 18, .commute 19, .commute 20, .braid 21, .commute 19,
    .commute 17, .commute 7, .commute 8, .commute 9, .braid 10, .commute 12, .commute 13,
    .commute 14, .commute 15, .commute 16, .braid 17, .braid 19, .commute 21, .commute 16,
    .commute 17])
,
  ([0, 5, 1, 0, 8, 0, 5, 2, 1, 0, 5, 6, 8, 2, 3, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2, 3, 2, 1], [0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1,
    0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2, 3, 2,
    1], [.commute 14, .commute 15, .commute 16, .commute 11, .commute 10, .braid 3, .commute 5,
    .commute 6, .commute 7, .braid 8, .commute 1, .commute 2, .braid 3, .commute 5, .braid 6,
    .commute 8, .commute 1])
,
  ([0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2, 3, 2, 1, 2], [0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2, 3, 1,
    2, 1], [.braid 44])
,
  ([0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2, 3, 1, 2, 1, 6], [0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 2,
    3, 1, 2, 1], [.commute 46, .commute 45, .commute 44, .commute 43, .commute 42, .commute 37,
    .commute 38, .commute 39, .braid 40, .commute 36, .commute 37, .braid 38, .commute 40,
    .commute 35, .braid 36, .commute 38, .commute 39])
,
  ([0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 2, 3, 1, 2, 1, 3], [0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5,
    1, 2, 3, 1, 2, 1], [.commute 47, .commute 44, .braid 45, .braid 43, .commute 45])
,
  ([0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 1, 2, 3, 1, 2, 1, 0], [0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0,
    5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0,
    5, 1, 2, 3, 1, 2, 1, 0], [])
,
  ([0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 1, 2, 3, 1, 2, 1, 0, 1], [0, 8, 1, 0, 5, 2, 1, 0, 8, 1,
    0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 1,
    0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [.braid 48])
,
  ([0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 2, 1, 0, 5, 6, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0, 5], [0, 8, 1, 0, 5, 2, 1, 0, 8,
    1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6,
    3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1], [.braid 48, .commute 50, .commute 42, .commute 43,
    .commute 44, .commute 45, .commute 46, .commute 47, .braid 48, .braid 45, .commute 47,
    .commute 48, .braid 40, .commute 42, .commute 43, .commute 44, .braid 45, .commute 47,
    .braid 42, .commute 44, .commute 45, .commute 46, .commute 41, .braid 42, .commute 44,
    .commute 45, .commute 40, .commute 41, .braid 42, .commute 44])
,
  ([0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 8], [0, 8, 1, 0, 5, 2, 1, 0,
    8, 1, 0, 5, 6, 2, 1, 3, 2, 5, 0, 1, 8, 0, 5, 6, 2, 3, 8, 0, 1, 2, 5, 0, 8, 0, 1, 0, 5, 6, 3,
    0, 1, 2, 8, 0, 1, 5, 0, 8, 5, 2, 3, 2, 1], [.commute 51, .commute 49, .commute 50, .commute
    47, .commute 48, .commute 49, .braid 45, .commute 47, .commute 48, .commute 44, .commute 45,
    .commute 43, .braid 41, .braid 43, .braid 45, .commute 47, .commute 34, .commute 35,
    .commute 33, .braid 31, .braid 33, .braid 35, .commute 37, .commute 38, .commute 39,
    .commute 40, .commute 41, .commute 29, .commute 30, .commute 31, .commute 28, .commute 27,
    .braid 28, .commute 30, .braid 31, .commute 33, .commute 34, .braid 35, .commute 37,
    .commute 38, .commute 33, .commute 21, .braid 19, .braid 21, .commute 23, .commute 24,
    .commute 25, .commute 26, .commute 16, .commute 17, .commute 15, .commute 16, .braid 17,
    .commute 19, .commute 20, .braid 21, .commute 23, .commute 24, .commute 25, .braid 26,
    .commute 28, .commute 29, .commute 30, .braid 31])
,
  ([0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 3, 2, 5, 0, 1, 8, 0, 5, 6, 2, 3, 8, 0, 1, 2, 5,
    0, 8, 0, 1, 0, 5, 6, 3, 0, 1, 2, 8, 0, 1, 5, 0, 8, 5, 2, 3, 2, 1], [0, 8, 1, 0, 5, 2, 1, 0,
    8, 1, 0, 5, 6, 2, 3, 5, 0, 1, 2, 3, 1, 0, 8, 5, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5, 6, 3, 5, 0, 1,
    8, 2, 0, 5, 1, 0, 8, 1, 0, 5, 2, 3, 2, 1], [.braid 33, .commute 35, .commute 36, .commute
    37, .braid 38, .commute 40, .braid 41, .commute 43, .commute 44, .braid 45, .commute 43,
    .commute 23, .commute 24, .commute 25, .commute 26, .commute 27, .commute 28, .commute 22,
    .commute 23, .commute 24, .commute 21, .commute 22, .commute 20, .commute 21, .braid 22,
    .braid 24, .commute 26, .commute 27, .braid 28, .commute 30, .commute 31, .commute 32,
    .commute 33, .braid 34, .commute 36, .commute 16, .commute 17, .braid 18, .commute 20,
    .commute 14, .commute 15, .braid 16, .commute 18, .commute 19, .braid 20, .commute 22,
    .commute 23, .braid 24, .commute 26, .commute 27, .braid 28, .commute 30, .commute 31,
    .braid 32, .commute 34, .commute 35, .braid 36, .commute 38, .commute 39, .commute 40,
    .braid 41, .braid 43, .commute 45, .commute 39])
,
  ([0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 2, 3, 5, 0, 1, 2, 3, 1, 0, 8, 5, 0, 1, 2, 6, 5, 0, 8,
    1, 0, 5, 6, 3, 5, 0, 1, 8, 2, 0, 5, 1, 0, 8, 1, 0, 5, 2, 3, 2, 1], [0, 8, 1, 0, 5, 2, 1, 0,
    8, 1, 0, 5, 6, 5, 0, 1, 2, 3, 2, 1, 0, 8, 5, 0, 1, 2, 3, 5, 6, 0, 5, 1, 0, 8, 0, 1, 5, 0, 6,
    5, 2, 1, 6, 0, 8, 2, 1, 0, 5, 2, 3, 2, 1], [.commute 40, .commute 41, .commute 38, .commute
    30, .commute 14, .commute 15, .commute 16, .braid 17, .commute 13, .commute 14, .braid 15,
    .commute 17, .braid 18, .commute 20, .commute 21, .commute 22, .commute 23, .braid 24,
    .commute 26, .commute 27, .braid 28, .braid 30, .commute 32, .commute 33, .commute 34,
    .commute 35, .braid 36, .braid 38, .commute 40, .braid 41, .commute 43, .commute 44,
    .commute 33, .commute 32, .braid 33, .commute 35, .commute 36, .commute 37, .commute 38,
    .commute 31, .commute 32, .braid 33, .commute 35, .commute 36, .commute 30, .commute 31,
    .commute 32, .braid 33, .commute 29, .commute 30, .commute 31, .commute 28, .commute 29,
    .commute 27, .commute 26, .braid 27, .braid 29, .braid 31, .commute 33, .braid 34, .braid
    36, .braid 38, .commute 40, .commute 41])
,
  ([0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 5, 0, 1, 2, 3, 2, 1, 0, 8, 5, 0, 1, 2, 3, 5, 6, 0, 5,
    1, 0, 8, 0, 1, 5, 0, 6, 5, 2, 1, 6, 0, 8, 2, 1, 0, 5, 2, 3, 2, 1], [0, 8, 1, 0, 5, 2, 0, 1,
    8, 0, 5, 6, 5, 3, 2, 1, 0, 8, 5, 0, 1, 2, 3, 0, 5, 6, 1, 0, 5, 2, 1, 0, 8, 0, 5, 6, 1, 2, 0,
    1, 0, 5, 0, 8, 6, 2, 1, 0, 5, 2, 3, 2, 1], [.commute 42, .commute 43, .commute 39, .commute
    40, .commute 37, .commute 38, .commute 35, .commute 36, .braid 16, .commute 18, .commute 19,
    .commute 20, .commute 21, .commute 22, .commute 23, .braid 24, .commute 26, .commute 27,
    .commute 28, .commute 29, .commute 15, .braid 16, .commute 18, .commute 19, .commute 20,
    .commute 21, .braid 22, .commute 24, .commute 25, .commute 26, .commute 14, .commute 15,
    .braid 16, .commute 18, .commute 19, .braid 20, .commute 22, .commute 23, .commute 8, .braid
    6, .braid 8, .commute 10, .commute 11, .commute 12, .commute 13, .commute 14, .commute 15,
    .braid 16, .braid 18, .commute 20, .commute 21, .commute 22, .braid 23, .commute 25, .braid
    26, .commute 28, .braid 29, .commute 31, .commute 32, .commute 33, .commute 34, .commute 35,
    .braid 36, .braid 38])
,
  ([0, 8, 1, 0, 5, 2, 0, 1, 8, 0, 5, 6, 5, 3, 2, 1, 0, 8, 5, 0, 1, 2, 3, 0, 5, 6, 1, 0, 5, 2, 1,
    0, 8, 0, 5, 6, 1, 2, 0, 1, 0, 5, 0, 8, 6, 2, 1, 0, 5, 2, 3, 2, 1], [0, 8, 1, 2, 5, 0, 8, 1,
    0, 5, 6, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5, 6, 5, 0, 1, 2, 8, 0, 5,
    1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2, 3, 2, 1], [.braid 40, .commute 42, .braid 31, .commute 33,
    .commute 34, .commute 35, .commute 36, .commute 28, .commute 29, .commute 30, .braid 31,
    .commute 33, .commute 29, .commute 27, .commute 17, .commute 12, .commute 13, .commute 14,
    .braid 15, .braid 17, .commute 19, .commute 20, .commute 21, .commute 4, .commute 3, .braid
    4, .commute 6, .commute 7, .braid 8, .commute 10, .commute 11, .commute 12, .braid 13,
    .commute 15, .commute 16, .braid 17, .commute 19, .commute 20, .braid 21, .commute 23,
    .commute 24, .commute 25, .commute 26, .braid 27, .braid 29, .commute 31, .commute 32,
    .braid 33, .commute 35, .braid 36, .commute 38, .commute 39, .braid 40, .commute 38,
    .commute 24, .commute 25, .commute 26, .commute 27, .commute 28, .commute 29, .braid 30,
    .commute 23, .commute 24, .commute 6])
,
  ([0, 8, 1, 2, 5, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0, 5, 8, 0, 1, 2, 3, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5,
    6, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 0, 5, 6, 2, 1, 0, 5, 2, 3, 2, 1], [0, 1, 2, 5, 0, 8, 1, 0,
    5, 6, 3, 2, 1, 0, 5, 0, 8, 1, 2, 3, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 5, 0, 8, 1, 0, 5, 3, 2, 1,
    0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 2, 3, 2, 1], [.commute 1, .commute 2, .commute 3, .braid 4,
    .braid 6, .commute 8, .commute 9, .commute 10, .braid 11, .commute 13, .commute 14, .commute
    15, .commute 16, .braid 17, .commute 19, .commute 20, .braid 21, .commute 23, .braid 24,
    .commute 26, .commute 27, .braid 28, .commute 30, .braid 31, .commute 33, .commute 34,
    .commute 35, .braid 36, .braid 38, .commute 40, .commute 34, .commute 35, .commute 36,
    .commute 19, .commute 20, .commute 21, .commute 18, .commute 19, .commute 17, .braid 15,
    .braid 17, .braid 19, .braid 21, .commute 23, .commute 24, .commute 25, .commute 26,
    .commute 27, .commute 28, .commute 29, .commute 30, .commute 31, .commute 32, .commute 33,
    .commute 34, .commute 35, .commute 32, .commute 22, .commute 23, .commute 24, .commute 20,
    .commute 21, .commute 18, .commute 19])
,
  ([0, 1, 2, 5, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 8, 1, 2, 3, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 5,
    0, 8, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 2, 3, 2, 1], [0, 1, 2, 5, 0, 8, 1, 0,
    3, 2, 1, 6, 5, 0, 8, 1, 0, 2, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1,
    0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 2, 3, 2, 1], [.braid 13, .commute 15, .commute 16, .commute
    17, .commute 18, .braid 19, .braid 21, .commute 23, .braid 24, .commute 26, .commute 27,
    .commute 28, .commute 29, .commute 30, .commute 31, .braid 27, .commute 29, .commute 30,
    .commute 26, .braid 27, .commute 29, .commute 23, .commute 24, .commute 25, .commute 26,
    .braid 27, .commute 24, .commute 25, .commute 22, .commute 23, .commute 20, .commute 21,
    .commute 9, .commute 10, .commute 11, .commute 8, .commute 9, .commute 10, .braid 11,
    .commute 13, .commute 14, .commute 15, .commute 16, .commute 17, .commute 18, .commute 19,
    .commute 20, .braid 21, .braid 23, .braid 25, .commute 27, .commute 20, .commute 21,
    .commute 22, .commute 23, .commute 17, .commute 18, .commute 19, .commute 20, .commute 21,
    .commute 22, .commute 18, .commute 19, .commute 16])
,
  ([0, 1, 2, 5, 0, 8, 1, 0, 3, 2, 1, 6, 5, 0, 8, 1, 0, 2, 5, 6, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 2, 3, 2, 1], [0, 5, 1, 0, 8, 6, 2, 1,
    0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1,
    0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 2, 3, 2, 1], [.commute 17, .commute 18, .commute 10, .commute
    11, .commute 9, .commute 10, .commute 8, .commute 9, .commute 7, .commute 6, .commute 2,
    .commute 3, .commute 4, .commute 5, .commute 1])
,
  ([0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 2, 3, 2, 1, 2], [0, 5, 1, 0, 8, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2,
    1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 2, 3, 1, 2, 1], [.braid 51])
,
  ([0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 2, 3, 1, 2, 1, 6], [0, 5, 1, 0, 8, 6,
    2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3,
    2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 2, 3, 1, 2, 1], [.commute 53, .commute 52, .commute
    51, .commute 50, .commute 49, .commute 44, .commute 45, .commute 46, .braid 47, .commute 43,
    .commute 44, .braid 45, .commute 47, .commute 42, .braid 43, .commute 45, .commute 46,
    .braid 41, .commute 43, .commute 44, .commute 45])
,
  ([0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 2, 3, 1, 2, 1, 3], [0, 5, 1, 0, 8,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5,
    3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 3, 1, 2, 1], [.commute 54, .commute 51,
    .braid 52, .braid 50, .commute 52])
,
  ([0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 3, 1, 2, 1, 0], [0, 5, 1, 0,
    8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0,
    5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 3, 1, 2, 1, 0], [])
,
  ([0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 3, 1, 2, 1, 0, 1], [0, 5, 1,
    0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1,
    0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [.braid 55])
,
  ([0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0, 5], [0, 5,
    1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2,
    1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [.commute 49,
    .commute 50, .commute 51, .commute 52, .commute 53, .braid 47, .commute 49, .commute 50,
    .commute 46, .braid 47, .commute 49, .braid 50, .commute 52, .braid 53, .commute 55, .braid
    56, .braid 54, .commute 56, .commute 53, .braid 54, .braid 51, .commute 53, .commute 54,
    .commute 50, .braid 51, .commute 53, .braid 48, .commute 50, .commute 51, .commute 52,
    .commute 47, .braid 48, .commute 50, .commute 51, .commute 46, .commute 47, .braid 48,
    .commute 50])
,
  ([0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0, 8], [0,
    5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 2, 1, 3, 5, 2, 6, 5, 0, 1, 8, 0, 5, 6, 2, 3,
    8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 1, 2, 0, 1, 8, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0, 8],
    [.commute 40, .commute 41, .commute 39, .braid 37, .braid 39, .braid 41, .commute 43,
    .commute 44, .commute 45, .commute 46, .commute 47, .commute 35, .commute 36, .commute 37,
    .commute 34, .commute 33, .braid 34, .commute 36, .braid 37, .commute 39, .commute 40,
    .braid 41, .commute 43, .commute 44, .commute 45, .commute 39, .commute 27, .braid 25,
    .braid 27, .commute 29, .commute 30, .commute 31, .commute 32, .commute 22, .commute 23,
    .commute 21, .commute 22, .braid 23, .commute 25, .commute 26, .braid 27, .commute 29,
    .commute 30, .commute 31, .braid 32, .commute 34, .commute 35, .commute 36, .braid 37,
    .braid 39, .commute 41, .commute 42, .commute 43, .commute 35, .commute 36, .commute 37,
    .commute 34, .commute 18, .commute 19, .commute 20, .commute 21, .commute 17, .commute 18,
    .commute 19])
,
  ([0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 2, 1, 3, 5, 2, 6, 5, 0, 1, 8, 0, 5, 6, 2,
    3, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 3, 1, 2, 0, 1, 8, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0, 8], [0,
    5, 1, 0, 8, 6, 2, 1, 0, 5, 0, 8, 1, 0, 2, 3, 1, 2, 1, 6, 5, 0, 1, 8, 0, 5, 6, 0, 8, 1, 0, 5,
    2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 2, 3, 1, 2, 0, 1, 8, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0, 8],
    [.commute 20, .braid 21, .commute 23, .commute 24, .commute 25, .commute 26, .braid 27,
    .commute 29, .commute 30, .commute 31, .braid 32, .braid 34, .commute 36, .braid 37,
    .commute 39, .commute 40, .commute 41, .commute 30, .commute 31, .commute 32, .commute 33,
    .commute 34, .commute 35, .commute 29, .commute 30, .commute 31, .commute 24, .commute 14,
    .braid 12, .braid 14, .commute 16, .commute 17, .commute 18, .commute 19, .commute 20,
    .commute 21, .braid 22, .braid 24, .commute 26, .commute 27, .commute 28, .commute 15,
    .commute 13, .commute 11, .commute 12, .braid 13, .braid 15, .commute 17, .commute 18,
    .commute 19, .braid 20, .commute 22, .commute 23, .braid 24, .commute 26, .commute 22,
    .commute 16, .commute 14, .commute 10, .commute 11, .commute 12, .commute 13, .braid 14,
    .braid 16])
,
  ([0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 0, 8, 1, 0, 2, 3, 1, 2, 1, 6, 5, 0, 1, 8, 0, 5, 6, 0, 8, 1, 0,
    5, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 2, 3, 1, 2, 0, 1, 8, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0, 8], [0,
    5, 1, 0, 8, 6, 2, 1, 0, 5, 0, 8, 1, 0, 2, 3, 1, 6, 0, 2, 5, 1, 0, 8, 0, 5, 6, 1, 2, 0, 1, 5,
    0, 8, 3, 2, 1, 0, 5, 6, 2, 3, 1, 2, 5, 0, 1, 8, 0, 5, 1, 2, 3, 1, 2, 8, 0, 1, 0, 8],
    [.commute 18, .commute 19, .braid 20, .braid 22, .commute 24, .commute 25, .braid 26, .braid
    28, .commute 30, .braid 31, .commute 33, .commute 34, .braid 35, .commute 37, .commute 38,
    .commute 39, .commute 40, .braid 41, .braid 43, .braid 45, .braid 47, .commute 49, .commute
    50, .commute 51, .commute 52, .commute 53, .commute 54, .commute 25, .commute 26, .commute
    27, .commute 28, .braid 23, .commute 25, .commute 26, .commute 22, .braid 23, .commute 21,
    .braid 19, .braid 21, .commute 23, .braid 24, .braid 26, .braid 28, .commute 30, .commute
    31, .commute 32, .commute 33, .commute 34, .commute 35, .commute 36, .commute 37, .braid 38,
    .commute 40, .commute 41, .commute 42, .commute 43, .commute 29, .commute 30, .commute 27,
    .commute 28, .commute 25, .commute 26, .commute 17, .commute 18])
,
  ([0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 0, 8, 1, 0, 2, 3, 1, 6, 0, 2, 5, 1, 0, 8, 0, 5, 6, 1, 2, 0, 1,
    5, 0, 8, 3, 2, 1, 0, 5, 6, 2, 3, 1, 2, 5, 0, 1, 8, 0, 5, 1, 2, 3, 1, 2, 8, 0, 1, 0, 8], [0,
    5, 1, 0, 8, 6, 2, 1, 0, 5, 0, 1, 2, 3, 1, 2, 0, 8, 1, 0, 6, 5, 6, 0, 1, 2, 8, 0, 5, 1, 0, 8,
    3, 2, 1, 0, 5, 6, 1, 2, 3, 0, 1, 2, 5, 0, 1, 8, 0, 5, 1, 2, 3, 1, 2, 8, 0, 1, 0, 8],
    [.commute 19, .commute 16, .commute 13, .commute 14, .commute 15, .braid 16, .commute 18,
    .braid 19, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25, .braid 26,
    .braid 28, .braid 30, .commute 32, .commute 33, .commute 34, .commute 35, .braid 36,
    .commute 38, .commute 39, .commute 40, .braid 21, .commute 23, .commute 24, .commute 25,
    .commute 26, .commute 18, .commute 19, .commute 20, .braid 21, .commute 23, .commute 19,
    .commute 17, .commute 11, .commute 12, .commute 13, .commute 14, .commute 15, .commute 16,
    .braid 17, .braid 19, .commute 21, .commute 22, .braid 23, .commute 25, .braid 26, .commute
    28, .commute 29, .braid 30, .commute 32, .commute 33, .braid 34, .commute 36, .commute 37,
    .commute 28, .commute 14, .commute 15, .commute 16, .commute 17, .commute 18, .commute 19])
,
  ([0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 0, 1, 2, 3, 1, 2, 0, 8, 1, 0, 6, 5, 6, 0, 1, 2, 8, 0, 5, 1, 0,
    8, 3, 2, 1, 0, 5, 6, 1, 2, 3, 0, 1, 2, 5, 0, 1, 8, 0, 5, 1, 2, 3, 1, 2, 8, 0, 1, 0, 8], [0,
    5, 1, 0, 8, 6, 5, 1, 0, 2, 1, 3, 2, 5, 0, 8, 1, 0, 5, 3, 6, 5, 0, 1, 8, 0, 5, 2, 3, 1, 2, 0,
    1, 8, 0, 5, 6, 1, 2, 3, 0, 1, 2, 5, 0, 8, 1, 0, 5, 0, 1, 2, 3, 1, 2, 8, 0, 1, 0, 8], [.braid
    20, .braid 8, .commute 10, .commute 11, .commute 12, .commute 13, .commute 14, .commute 7,
    .braid 8, .commute 10, .commute 11, .commute 6, .commute 7, .braid 8, .commute 10, .braid
    11, .commute 13, .braid 14, .commute 16, .commute 17, .braid 18, .commute 20, .braid 21,
    .commute 23, .commute 24, .commute 25, .braid 26, .braid 28, .commute 30, .commute 31,
    .braid 32, .commute 34, .commute 35, .commute 36, .braid 37, .commute 39, .braid 40,
    .commute 42, .braid 43, .commute 45, .commute 46, .braid 47, .commute 45, .commute 30,
    .commute 31, .commute 32, .commute 29, .commute 30, .commute 28, .commute 24, .commute 25,
    .commute 26, .commute 10, .commute 11, .commute 9, .braid 7, .braid 9, .braid 11, .commute
    13, .commute 14, .commute 15, .commute 16, .commute 17, .commute 18])
,
  ([0, 5, 1, 0, 8, 6, 5, 1, 0, 2, 1, 3, 2, 5, 0, 8, 1, 0, 5, 3, 6, 5, 0, 1, 8, 0, 5, 2, 3, 1, 2,
    0, 1, 8, 0, 5, 6, 1, 2, 3, 0, 1, 2, 5, 0, 8, 1, 0, 5, 0, 1, 2, 3, 1, 2, 8, 0, 1, 0, 8], [0,
    5, 6, 0, 1, 2, 0, 3, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3, 8, 0, 1, 2, 5, 0, 8, 1,
    0, 5, 6, 0, 1, 2, 3, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5, 0, 1, 2, 3, 1, 2, 8, 0, 1, 0, 8],
    [.commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute 24, .commute 25,
    .braid 26, .braid 28, .braid 30, .braid 32, .commute 34, .commute 35, .commute 36, .commute
    37, .commute 38, .commute 25, .commute 26, .commute 27, .commute 28, .commute 24, .commute
    25, .commute 22, .commute 12, .commute 13, .commute 14, .commute 10, .commute 11, .commute
    8, .commute 9, .commute 6, .commute 7, .commute 8, .braid 9, .braid 11, .commute 13, .braid
    14, .commute 16, .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .braid 22,
    .commute 24, .braid 25, .commute 27, .braid 28, .commute 30, .commute 31, .braid 32,
    .commute 34, .commute 30, .commute 21, .commute 22, .commute 23, .commute 4, .commute 5,
    .commute 6, .commute 7, .commute 3, .commute 2, .braid 3, .commute 5])
,
  ([0, 5, 6, 0, 1, 2, 0, 3, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 6, 5, 0, 1, 2, 3, 8, 0, 1, 2, 5, 0, 8,
    1, 0, 5, 6, 0, 1, 2, 3, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5, 0, 1, 2, 3, 1, 2, 8, 0, 1, 0, 8], [0,
    5, 6, 0, 1, 2, 3, 8, 0, 1, 5, 2, 6, 0, 5, 8, 0, 1, 2, 3, 0, 8, 5, 0, 1, 2, 6, 5, 0, 8, 1, 0,
    5, 6, 0, 1, 2, 3, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1, 2, 8, 0, 1, 0, 8],
    [.commute 6, .braid 7, .commute 9, .commute 10, .braid 11, .commute 13, .braid 14, .commute
    16, .commute 17, .commute 18, .braid 19, .commute 21, .commute 22, .braid 23, .commute 25,
    .commute 26, .commute 27, .braid 28, .braid 30, .commute 32, .commute 33, .braid 34,
    .commute 36, .commute 37, .braid 38, .commute 40, .commute 41, .commute 42, .braid 43,
    .braid 45, .commute 47, .braid 48, .commute 50, .commute 51, .commute 41, .commute 42,
    .commute 43, .commute 40, .braid 16, .commute 18, .commute 19, .commute 20, .commute 21,
    .commute 22, .commute 23, .commute 24, .commute 25, .commute 15, .braid 16, .commute 18,
    .commute 19, .commute 20, .commute 21, .commute 14, .commute 15, .braid 16, .commute 18,
    .commute 19, .commute 12, .commute 13, .commute 14, .commute 11, .commute 12, .commute 9])
,
  ([0, 5, 6, 0, 1, 2, 3, 8, 0, 1, 5, 2, 6, 0, 5, 8, 0, 1, 2, 3, 0, 8, 5, 0, 1, 2, 6, 5, 0, 8, 1,
    0, 5, 6, 0, 1, 2, 3, 8, 0, 5, 1, 0, 8, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1, 2, 8, 0, 1, 0, 8], [5,
    0, 1, 2, 3, 8, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 3, 1, 0, 8, 5, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5, 6,
    5, 0, 1, 2, 3, 8, 5, 0, 5, 1, 0, 8, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1, 2, 8, 0, 1, 0, 8],
    [.commute 10, .commute 2, .commute 3, .commute 4, .commute 5, .commute 6, .commute 7,
    .commute 8, .commute 9, .braid 10, .braid 12, .braid 14, .commute 16, .commute 17, .commute
    18, .braid 19, .braid 21, .commute 23, .commute 24, .braid 25, .commute 27, .commute 28,
    .commute 29, .commute 30, .braid 31, .commute 9, .commute 10, .commute 11, .commute 12,
    .commute 13, .commute 14, .braid 15, .commute 17, .commute 8, .commute 9, .braid 0, .commute
    2, .commute 3, .commute 4, .commute 5, .braid 6, .commute 8, .braid 9, .commute 11, .commute
    12, .braid 13, .commute 15, .commute 16, .braid 17, .commute 19, .commute 20, .braid 21,
    .commute 23, .commute 24, .braid 25, .commute 27, .commute 28, .braid 29, .commute 31,
    .braid 32, .commute 34, .commute 35, .commute 36, .commute 37])
,
  ([5, 0, 1, 2, 3, 8, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 3, 1, 0, 8, 5, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5,
    6, 5, 0, 1, 2, 3, 8, 5, 0, 5, 1, 0, 8, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1, 2, 8, 0, 1, 0, 8], [5,
    0, 1, 2, 3, 8, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 3, 1, 0, 8, 5, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5, 6,
    5, 0, 1, 8, 0, 5, 1, 2, 3, 1, 0, 1, 2, 8, 0, 1, 5, 0, 8, 5, 1, 2, 3, 1, 2, 0, 1, 0], [.braid
    38, .braid 40, .commute 42, .braid 43, .commute 45, .commute 46, .commute 47, .braid 48,
    .commute 50, .braid 51, .commute 53, .braid 54, .commute 56, .braid 57, .braid 55, .commute
    57, .commute 54, .braid 55, .braid 52, .commute 54, .commute 55, .commute 51, .braid 52,
    .commute 54, .braid 49, .commute 51, .commute 52, .commute 53, .commute 48, .braid 49,
    .commute 51, .commute 52, .commute 47, .commute 48, .braid 49, .commute 51, .commute 46,
    .commute 47, .commute 48, .commute 45, .commute 46, .commute 44, .commute 36, .commute 37,
    .commute 38, .commute 39, .commute 40, .commute 41, .braid 42, .braid 44, .braid 46, .braid
    48, .commute 50, .commute 41, .commute 42, .commute 43, .commute 44, .commute 40, .commute
    41, .commute 35, .commute 36, .commute 37, .braid 38, .commute 40])
,
  ([5, 0, 1, 2, 3, 8, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 3, 1, 0, 8, 5, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5,
    6, 5, 0, 1, 8, 0, 5, 1, 2, 3, 1, 0, 1, 2, 8, 0, 1, 5, 0, 8, 5, 1, 2, 3, 1, 2, 0, 1, 0], [5,
    0, 1, 2, 3, 8, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 3, 1, 0, 8, 5, 0, 1, 2, 6, 5, 0, 1, 0, 8, 5, 0,
    6, 5, 6, 1, 0, 8, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [.braid
    41, .commute 43, .braid 44, .commute 46, .commute 47, .braid 48, .commute 46, .commute 37,
    .commute 38, .commute 39, .commute 34, .braid 35, .commute 37, .commute 38, .braid 39,
    .commute 41, .commute 42, .commute 43, .braid 44, .braid 46, .commute 48, .commute 42,
    .commute 43, .commute 44, .commute 41, .braid 33, .commute 35, .commute 36, .commute 37,
    .commute 38, .braid 39, .braid 41, .commute 43, .braid 44, .commute 46, .commute 47,
    .commute 37, .commute 38, .commute 39, .commute 40, .commute 41, .commute 42, .commute 36,
    .commute 37, .commute 38, .commute 35, .commute 32, .braid 33, .braid 35, .commute 37,
    .braid 38, .commute 40, .commute 41, .braid 42, .commute 44, .commute 45, .commute 46,
    .commute 31, .commute 32, .commute 30, .commute 27, .braid 28, .braid 30, .braid 32])
,
  ([5, 0, 1, 2, 3, 8, 0, 5, 6, 1, 0, 5, 8, 0, 1, 2, 3, 1, 0, 8, 5, 0, 1, 2, 6, 5, 0, 1, 0, 8, 5,
    0, 6, 5, 6, 1, 0, 8, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [5,
    0, 1, 2, 8, 0, 5, 6, 1, 0, 5, 8, 0, 1, 3, 2, 3, 1, 2, 0, 1, 8, 0, 5, 6, 0, 8, 1, 0, 5, 2, 1,
    0, 8, 1, 2, 0, 1, 5, 0, 6, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0],
    [.commute 34, .commute 35, .commute 36, .commute 37, .commute 38, .commute 39, .commute 33,
    .commute 31, .braid 26, .commute 28, .commute 29, .commute 30, .braid 31, .braid 33,
    .commute 35, .commute 36, .commute 37, .commute 28, .commute 29, .commute 25, .braid 26,
    .commute 28, .braid 29, .commute 31, .commute 32, .braid 33, .commute 35, .commute 31,
    .commute 24, .commute 25, .braid 26, .commute 28, .braid 29, .braid 31, .commute 33, .braid
    22, .commute 24, .commute 25, .commute 26, .commute 27, .commute 28, .commute 29, .commute
    21, .braid 22, .commute 24, .commute 25, .commute 26, .commute 20, .commute 21, .braid 22,
    .commute 24, .commute 19, .commute 20, .commute 18, .commute 4, .commute 5, .commute 6,
    .commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .commute 12, .commute 13])
,
  ([5, 0, 1, 2, 8, 0, 5, 6, 1, 0, 5, 8, 0, 1, 3, 2, 3, 1, 2, 0, 1, 8, 0, 5, 6, 0, 8, 1, 0, 5, 2,
    1, 0, 8, 1, 2, 0, 1, 5, 0, 6, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [5,
    0, 1, 2, 8, 0, 5, 6, 1, 0, 5, 2, 3, 1, 8, 2, 0, 8, 1, 0, 5, 6, 0, 8, 2, 1, 0, 5, 3, 2, 1, 0,
    8, 1, 0, 5, 6, 2, 3, 1, 2, 0, 1, 5, 0, 8, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [.braid
    14, .braid 16, .braid 18, .braid 20, .commute 22, .commute 23, .braid 24, .braid 26,
    .commute 28, .braid 29, .commute 31, .commute 32, .braid 33, .braid 35, .braid 37, .braid
    39, .commute 41, .commute 42, .commute 43, .commute 44, .commute 45, .commute 40, .commute
    41, .commute 42, .commute 38, .commute 39, .commute 40, .commute 36, .commute 37, .commute
    38, .commute 34, .commute 35, .commute 36, .commute 15, .braid 13, .braid 15, .commute 17,
    .commute 18, .commute 19, .commute 20, .commute 21, .commute 22, .commute 23, .commute 24,
    .commute 25, .commute 26, .commute 27, .commute 16, .commute 14, .commute 12, .commute 13,
    .braid 14, .braid 16, .commute 18, .commute 19, .commute 20, .commute 21, .commute 22,
    .commute 23, .commute 17, .commute 15, .commute 11, .commute 12, .commute 13])
,
  ([5, 0, 1, 2, 8, 0, 5, 6, 1, 0, 5, 2, 3, 1, 8, 2, 0, 8, 1, 0, 5, 6, 0, 8, 2, 1, 0, 5, 3, 2, 1,
    0, 8, 1, 0, 5, 6, 2, 3, 1, 2, 0, 1, 5, 0, 8, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [5,
    0, 1, 8, 0, 5, 6, 1, 2, 3, 0, 1, 2, 5, 0, 8, 1, 0, 5, 6, 1, 0, 2, 8, 1, 3, 2, 5, 0, 8, 1, 0,
    5, 6, 2, 3, 0, 1, 2, 8, 0, 1, 5, 0, 8, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0],
    [.commute 14, .braid 15, .braid 17, .commute 19, .commute 20, .commute 10, .commute 11,
    .commute 12, .commute 13, .commute 9, .commute 10, .commute 3, .commute 4, .commute 5,
    .commute 6, .braid 7, .commute 9, .braid 10, .commute 12, .braid 13, .commute 15, .commute
    16, .braid 17, .commute 19, .braid 20, .commute 22, .braid 23, .commute 25, .commute 26,
    .braid 27, .commute 29, .commute 30, .commute 31, .commute 32, .commute 33, .commute 34,
    .commute 35, .braid 36, .braid 38, .braid 40, .braid 42, .commute 44, .commute 31, .braid
    29, .braid 31, .commute 33, .commute 34, .commute 35, .commute 36, .commute 37, .commute 38,
    .commute 26, .commute 27, .commute 25, .commute 26, .braid 27, .commute 29, .commute 30,
    .braid 31, .commute 33, .commute 34, .commute 35, .commute 29, .commute 22])
,
  ([5, 0, 1, 8, 0, 5, 6, 1, 2, 3, 0, 1, 2, 5, 0, 8, 1, 0, 5, 6, 1, 0, 2, 8, 1, 3, 2, 5, 0, 8, 1,
    0, 5, 6, 2, 3, 0, 1, 2, 8, 0, 1, 5, 0, 8, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [5,
    0, 8, 0, 1, 2, 3, 5, 0, 1, 2, 6, 5, 0, 8, 0, 1, 0, 2, 3, 5, 0, 6, 5, 1, 0, 8, 2, 1, 0, 5, 6,
    1, 2, 3, 0, 1, 2, 8, 0, 5, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0],
    [.commute 23, .commute 24, .commute 25, .commute 26, .braid 27, .braid 29, .commute 31,
    .commute 32, .commute 25, .commute 26, .commute 27, .commute 23, .commute 24, .commute 21,
    .commute 22, .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .commute 11,
    .commute 5, .commute 6, .commute 7, .commute 2, .braid 3, .commute 5, .commute 6, .braid 7,
    .commute 9, .commute 10, .braid 11, .commute 13, .commute 14, .commute 15, .commute 16,
    .braid 17, .commute 19, .commute 20, .commute 21, .braid 22, .braid 24, .commute 26, .braid
    27, .commute 29, .commute 30, .commute 31, .braid 32, .commute 34, .braid 35, .commute 37,
    .braid 38, .commute 40, .commute 41, .braid 42, .commute 40, .commute 18, .commute 19,
    .commute 20, .commute 21, .commute 17, .commute 18, .commute 19, .braid 15])
,
  ([5, 0, 8, 0, 1, 2, 3, 5, 0, 1, 2, 6, 5, 0, 8, 0, 1, 0, 2, 3, 5, 0, 6, 5, 1, 0, 8, 2, 1, 0, 5,
    6, 1, 2, 3, 0, 1, 2, 8, 0, 5, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [5,
    8, 0, 1, 2, 3, 5, 6, 0, 8, 5, 0, 1, 2, 3, 0, 5, 6, 8, 0, 1, 5, 0, 8, 2, 0, 1, 0, 5, 6, 0, 1,
    2, 3, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0],
    [.commute 17, .commute 18, .braid 19, .braid 21, .commute 23, .commute 24, .commute 25,
    .commute 26, .commute 27, .commute 28, .braid 29, .commute 31, .commute 32, .commute 33,
    .commute 22, .commute 20, .commute 10, .commute 11, .commute 12, .commute 13, .commute 14,
    .braid 15, .commute 17, .commute 18, .commute 19, .braid 20, .braid 22, .commute 24,
    .commute 25, .commute 26, .braid 27, .commute 29, .braid 12, .commute 14, .commute 15,
    .commute 16, .commute 17, .commute 18, .commute 9, .commute 10, .commute 11, .braid 12,
    .commute 14, .commute 15, .commute 10, .commute 8, .braid 1, .commute 3, .commute 4,
    .commute 5, .commute 6, .commute 7, .braid 8, .braid 10, .commute 12, .commute 13, .commute
    14, .braid 15, .commute 17, .braid 18, .commute 20, .commute 21, .braid 22, .commute 24])
,
  ([5, 8, 0, 1, 2, 3, 5, 6, 0, 8, 5, 0, 1, 2, 3, 0, 5, 6, 8, 0, 1, 5, 0, 8, 2, 0, 1, 0, 5, 6, 0,
    1, 2, 3, 5, 0, 1, 2, 8, 0, 5, 1, 0, 8, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [8,
    0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 3, 1, 0, 5, 6, 1, 8, 0, 1, 2, 5, 0, 1, 8, 0, 5, 6, 8, 0, 1, 2,
    3, 5, 0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [.braid
    25, .commute 27, .commute 28, .braid 29, .commute 31, .commute 32, .braid 33, .commute 35,
    .commute 36, .commute 37, .braid 38, .braid 40, .commute 42, .commute 36, .commute 37,
    .commute 38, .commute 35, .commute 23, .commute 24, .commute 22, .commute 20, .commute 5,
    .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .commute 11, .braid 12,
    .commute 14, .commute 15, .commute 16, .commute 17, .commute 18, .commute 19, .braid 20,
    .braid 22, .braid 24, .commute 26, .commute 27, .commute 19, .commute 20, .commute 4,
    .commute 5, .commute 6, .commute 7, .commute 8, .commute 9, .braid 10, .commute 12, .commute
    3, .commute 4, .commute 0, .braid 1, .commute 3, .braid 4, .commute 6, .commute 7, .braid 8,
    .commute 10, .commute 11, .braid 12, .commute 14, .commute 15])
,
  ([8, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 3, 1, 0, 5, 6, 1, 8, 0, 1, 2, 5, 0, 1, 8, 0, 5, 6, 8, 0, 1,
    2, 3, 5, 0, 8, 1, 0, 5, 2, 1, 0, 8, 1, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [8,
    0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 3, 1, 0, 5, 8, 0, 1, 2, 1, 0, 8, 6, 5, 6, 0, 5, 1, 0, 8, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0],
    [.commute 16, .braid 17, .commute 19, .braid 20, .commute 22, .commute 23, .braid 24,
    .commute 26, .braid 27, .commute 29, .commute 30, .commute 31, .commute 32, .braid 33,
    .braid 35, .commute 37, .braid 38, .commute 40, .commute 41, .commute 31, .commute 32,
    .commute 33, .commute 34, .commute 35, .commute 36, .commute 30, .commute 31, .commute 32,
    .commute 26, .commute 27, .commute 28, .commute 25, .braid 23, .braid 25, .commute 27,
    .braid 28, .commute 30, .commute 31, .braid 21, .commute 23, .commute 24, .braid 25,
    .commute 27, .braid 28, .commute 30, .commute 23, .commute 20, .braid 21, .braid 23,
    .commute 25, .commute 26, .commute 27, .braid 28, .commute 25, .commute 26, .commute 24,
    .commute 22, .commute 15, .commute 16, .commute 17, .commute 18, .commute 19, .commute 20,
    .commute 21])
,
  ([8, 0, 5, 6, 1, 0, 8, 5, 0, 1, 2, 3, 1, 0, 5, 8, 0, 1, 2, 1, 0, 8, 6, 5, 6, 0, 5, 1, 0, 8, 0,
    5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [8,
    0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5,
    6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0], [.braid
    22, .braid 24, .braid 26, .commute 28, .braid 17, .commute 19, .commute 20, .commute 21,
    .commute 22, .commute 23, .commute 24, .commute 11, .commute 12, .commute 13, .commute 14,
    .commute 15, .braid 9, .commute 11, .commute 12, .commute 13, .commute 14, .braid 15,
    .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .commute 22, .commute 23,
    .commute 14, .commute 15, .braid 16, .commute 18, .commute 19, .commute 20, .commute 8,
    .braid 9, .commute 11, .commute 12, .commute 13, .braid 14, .commute 16, .commute 17,
    .commute 18, .commute 19, .commute 12, .commute 13, .commute 14, .braid 15, .commute 7,
    .commute 8, .braid 9, .commute 11, .commute 12, .braid 13, .commute 15, .commute 3, .commute
    4, .commute 5])
,
  ([8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0,
    5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 1, 2, 0, 1, 0, 2],
    [8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1,
    0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 0, 1, 2, 0, 1,
    0], [.commute 59, .commute 56, .braid 57, .braid 55, .commute 57])
,
  ([8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0,
    5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 0, 1, 2, 0, 1, 0,
    6], [8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 0, 1, 2, 0,
    1, 0], [.commute 60, .commute 59, .commute 58, .commute 57, .commute 56, .commute 55,
    .commute 54, .commute 53, .commute 52, .commute 46, .commute 47, .commute 48, .commute 49,
    .braid 50, .commute 45, .commute 46, .commute 47, .braid 48, .commute 50, .commute 44,
    .commute 45, .braid 46, .commute 48, .commute 49, .commute 43, .braid 44, .commute 46,
    .commute 47, .commute 48, .braid 42, .commute 44, .commute 45, .commute 46, .commute 47])
,
  ([8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0,
    5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 1, 2, 3, 0, 1, 2, 0, 1, 0,
    3], [8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1, 2,
    0, 1, 0], [.commute 61, .commute 60, .commute 59, .commute 55, .commute 56, .braid 57,
    .commute 54, .braid 55, .commute 57, .braid 53, .commute 55, .commute 56])
,
  ([8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0,
    5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 0, 1, 2, 0, 1,
    0, 4], [8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0,
    8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0,
    1, 2, 0, 1, 0], [.commute 62, .commute 61, .commute 60, .commute 59, .commute 58, .commute
    57])
,
  ([8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0,
    5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 0,
    1, 0, 0], [8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1,
    0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4,
    0, 1, 2, 0, 1], [.square 63])
,
  ([8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0,
    5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 0,
    1, 1], [8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0,
    8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0,
    1, 2, 0], [.square 62])
,
  ([8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0,
    5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 3, 2, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 0,
    5], [8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8,
    1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1,
    0], [.braid 51, .commute 53, .commute 54, .commute 55, .commute 56, .commute 50, .braid 51,
    .commute 53, .commute 54, .commute 55, .braid 56, .commute 58, .commute 59, .commute 49,
    .commute 50, .braid 51, .commute 53, .commute 54, .commute 55, .braid 56, .commute 58,
    .braid 59, .square 61, .commute 48, .commute 49, .commute 50, .braid 51, .commute 53,
    .commute 54, .commute 55, .braid 56, .commute 58, .commute 57, .commute 56, .braid 54,
    .commute 53, .commute 54, .commute 52, .commute 53, .commute 51, .commute 52, .braid 49,
    .commute 51, .commute 48, .braid 49])
,
  ([8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 1, 0,
    5, 6, 2, 1, 0, 5, 3, 2, 1, 0, 8, 3, 2, 1, 0, 5, 6, 1, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0,
    8], [8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 0, 1, 8, 0, 5, 6, 2, 1, 3, 2, 5, 0, 8, 1, 0, 5,
    6, 0, 1, 2, 3, 0, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5, 6, 0, 1, 8, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1,
    0, 8], [.commute 41, .commute 42, .commute 43, .commute 40, .commute 41, .commute 39, .braid
    37, .braid 39, .braid 41, .braid 43, .commute 45, .commute 46, .commute 47, .commute 36,
    .commute 37, .commute 38, .commute 39, .commute 35, .commute 36, .braid 33, .commute 35,
    .braid 36, .commute 38, .braid 39, .commute 41, .commute 42, .braid 43, .commute 45,
    .commute 41, .commute 28, .braid 26, .braid 28, .commute 30, .commute 31, .commute 32,
    .commute 33, .commute 34, .commute 23, .commute 24, .commute 22, .commute 23, .braid 24,
    .commute 26, .commute 27, .braid 28, .commute 30, .commute 26, .commute 15, .braid 13,
    .braid 15, .commute 17, .commute 18, .commute 19, .commute 20, .commute 21, .commute 22,
    .commute 23, .braid 24, .braid 26, .commute 28, .commute 29, .braid 30, .commute 32,
    .commute 33])
,
  ([8, 0, 5, 1, 0, 8, 6, 2, 1, 0, 5, 3, 2, 0, 1, 8, 0, 5, 6, 2, 1, 3, 2, 5, 0, 8, 1, 0, 5, 6, 0,
    1, 2, 3, 0, 8, 0, 1, 2, 5, 0, 8, 1, 0, 5, 6, 0, 1, 8, 0, 5, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0,
    8], [8, 0, 5, 1, 0, 8, 6, 2, 1, 3, 2, 5, 0, 1, 8, 0, 5, 6, 2, 3, 1, 0, 5, 1, 8, 0, 1, 2, 3,
    1, 0, 8, 5, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5, 6, 5, 0, 1, 8, 0, 5, 8, 0, 1, 2, 3, 4, 0, 1, 2, 1,
    0, 8], [.braid 34, .commute 36, .commute 37, .commute 38, .braid 39, .braid 41, .commute 43,
    .commute 44, .braid 45, .braid 47, .commute 49, .commute 29, .commute 30, .commute 31,
    .commute 32, .commute 33, .commute 34, .commute 35, .commute 36, .braid 27, .commute 29,
    .commute 30, .commute 31, .commute 32, .commute 26, .braid 27, .commute 29, .commute 30,
    .commute 25, .braid 23, .braid 25, .commute 27, .commute 28, .commute 29, .braid 30, .braid
    32, .commute 34, .commute 35, .braid 36, .commute 38, .commute 39, .commute 40, .commute 41,
    .braid 42, .commute 22, .commute 23, .commute 24, .commute 25, .braid 26, .commute 28,
    .commute 20, .commute 10, .commute 11, .commute 9, .commute 10, .braid 11, .commute 13,
    .commute 14, .braid 15, .commute 17, .commute 18, .commute 19, .braid 20, .commute 22])
,
  ([8, 0, 5, 1, 0, 8, 6, 2, 1, 3, 2, 5, 0, 1, 8, 0, 5, 6, 2, 3, 1, 0, 5, 1, 8, 0, 1, 2, 3, 1, 0,
    8, 5, 0, 1, 2, 6, 5, 0, 8, 1, 0, 5, 6, 5, 0, 1, 8, 0, 5, 8, 0, 1, 2, 3, 4, 0, 1, 2, 1, 0,
    8], [8, 0, 5, 1, 0, 6, 2, 1, 3, 2, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 8, 0, 1, 2, 3, 2, 1, 0,
    8, 5, 0, 1, 2, 6, 5, 0, 1, 8, 0, 5, 6, 5, 8, 0, 8, 1, 0, 5, 8, 0, 1, 2, 3, 4, 8, 0, 1, 2, 1,
    0, 8], [.commute 23, .braid 24, .commute 26, .commute 27, .braid 28, .commute 30, .commute
    31, .braid 32, .commute 34, .commute 35, .braid 36, .commute 38, .commute 39, .braid 40,
    .commute 42, .braid 43, .commute 45, .commute 46, .braid 47, .braid 49, .commute 51,
    .commute 52, .commute 53, .commute 54, .commute 45, .commute 38, .commute 19, .commute 20,
    .commute 21, .commute 22, .commute 23, .commute 24, .braid 25, .commute 13, .commute 5,
    .commute 6, .commute 7, .commute 8, .commute 9, .commute 10, .braid 11, .braid 13, .commute
    15, .commute 16, .braid 17, .commute 19, .commute 20, .commute 21, .commute 22, .braid 23,
    .commute 25, .braid 26, .commute 28, .commute 29, .commute 30, .commute 31, .braid 32,
    .commute 34, .commute 35, .braid 36, .braid 38, .commute 40, .commute 41, .commute 42])
,
  ([8, 0, 5, 1, 0, 6, 2, 1, 3, 2, 5, 0, 8, 1, 0, 5, 6, 2, 1, 0, 5, 8, 0, 1, 2, 3, 2, 1, 0, 8, 5,
    0, 1, 2, 6, 5, 0, 1, 8, 0, 5, 6, 5, 8, 0, 8, 1, 0, 5, 8, 0, 1, 2, 3, 4, 8, 0, 1, 2, 1, 0,
    8], [8, 0, 5, 1, 0, 6, 2, 3, 5, 0, 1, 2, 8, 0, 8, 1, 5, 6, 0, 8, 5, 0, 1, 2, 3, 2, 1, 0, 5,
    6, 8, 0, 5, 1, 2, 0, 8, 1, 0, 5, 6, 5, 0, 8, 2, 1, 0, 5, 8, 0, 1, 2, 3, 4, 8, 0, 1, 2, 1, 8,
    0, 8], [.braid 43, .braid 45, .commute 47, .commute 48, .braid 49, .commute 51, .commute 52,
    .commute 53, .braid 54, .commute 56, .commute 57, .commute 58, .commute 33, .commute 34,
    .commute 35, .commute 32, .commute 33, .commute 31, .commute 16, .commute 17, .commute 18,
    .commute 15, .commute 16, .commute 14, .commute 9, .commute 10, .commute 11, .braid 12,
    .braid 14, .braid 16, .braid 18, .commute 20, .commute 21, .commute 22, .commute 23,
    .commute 24, .commute 25, .commute 26, .commute 27, .commute 28, .braid 29, .braid 31,
    .braid 33, .braid 35, .commute 37, .commute 38, .commute 39, .commute 40, .commute 41,
    .commute 42, .commute 43, .commute 36, .commute 34, .commute 28, .commute 29, .commute 19,
    .commute 17, .commute 11, .commute 12, .commute 7, .commute 8, .braid 9, .commute 11, .braid
    12])
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
