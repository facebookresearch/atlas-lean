/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Data.List.PairwiseIdxOf

@[expose] public section

example :
    ([2, 4, 8] : List Nat).idxOf 2 < [2, 4, 8].idxOf 8 ↔ 2 < 8 :=
  List.Pairwise.idxOf_lt_iff (f := id) (by decide) (by decide) (by decide)

example :
    ([2, 4, 8] : List Nat).idxOf 8 < [2, 4, 8].idxOf 2 ↔ 8 < 2 :=
  List.Pairwise.idxOf_lt_iff (f := id) (by decide) (by decide) (by decide)

example :
    ([7] : List Nat).idxOf 7 < [7].idxOf 7 ↔ 7 < 7 :=
  List.Pairwise.idxOf_lt_iff (f := id) (by decide) (by decide) (by decide)

example :
    ([false, true] : List Bool).idxOf false < [false, true].idxOf true ↔ 1 < 3 :=
  List.Pairwise.idxOf_lt_iff (f := fun | false => 1 | true => 3)
    (by decide) (by decide) (by decide)
