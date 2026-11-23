/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Data.List.PairwiseProduct

@[expose] public section

example :
    ([0, 1, 2].product [10, 20]).Pairwise (Prod.Lex (fun x y : Nat => x < y) (· < ·)) :=
  List.Pairwise.product_lex (by decide) (by decide)

example :
    (([] : List Nat).product [true]).Pairwise
      (Prod.Lex (fun x y : Nat => x < y) (fun x y : Bool => x < y)) :=
  List.Pairwise.product_lex List.Pairwise.nil (by decide)

example :
    ([0, 0].product [true]).Pairwise
      (Prod.Lex (fun _ _ : Nat => True) (fun _ _ : Bool => False)) :=
  List.Pairwise.product_lex (by simp) (by simp)
