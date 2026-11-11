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

private theorem idxOf_lt_iff_type_zero {α : Type} [BEq α] [LawfulBEq α]
    {f : α → ℕ} {l : List α} (hl : l.Pairwise fun x y => f x < f y)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
    l.idxOf x < l.idxOf y ↔ f x < f y :=
  List.Pairwise.idxOf_lt_iff hl hx hy

private def higherList : List (ULift.{1} Nat) :=
  [ULift.up 2, ULift.up 4, ULift.up 8]

example :
    higherList.idxOf (ULift.up 2) < higherList.idxOf (ULift.up 8) ↔ 2 < 8 :=
  List.Pairwise.idxOf_lt_iff (α := ULift.{1} Nat) (f := fun x => x.down)
    (l := higherList) (x := ULift.up 2) (y := ULift.up 8) (by decide)
    (by exact List.mem_cons_self) (by exact List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <|
      List.mem_cons_self)

example :
    higherList.idxOf (ULift.up 8) < higherList.idxOf (ULift.up 2) ↔ 8 < 2 :=
  List.Pairwise.idxOf_lt_iff (α := ULift.{1} Nat) (f := fun x => x.down)
    (l := higherList) (x := ULift.up 8) (y := ULift.up 2) (by decide)
    (by exact List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_self)
    (by exact List.mem_cons_self)
