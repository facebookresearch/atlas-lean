/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Data.List.SplitLengths

@[expose] public section

-- The exact independent Bool-list recursion from the pinned ETH source.
private def sourceChunks : List Nat → List Bool → List (List Bool)
  | [], _ => []
  | n :: ns, xs => xs.take n :: sourceChunks ns (xs.drop n)

example (lengths : List Nat) (xs : List Bool) :
    sourceChunks lengths xs = lengths.splitLengths xs := by
  induction lengths generalizing xs with
  | nil => rfl
  | cons n ns ih =>
      simp only [sourceChunks, List.splitLengths_cons, ih]

example :
    [2, 1, 0, 2].splitLengths [10, 11, 20, 30, 31] = [[10, 11], [20], [], [30, 31]] := by
  decide

example : [2, 2, 1, 3].splitLengths [10, 11, 20] = [[10, 11], [20], [], []] := by
  decide

example : ([] : List Nat).splitLengths [10, 11] = [] := by
  decide

example : [1, 0].splitLengths ([] : List Nat) = [[], []] := by
  decide

example : [0, 2, 0].splitLengths [10, 11] = [[], [10, 11], []] := by
  decide

example (width : ℕ) (widths : List ℕ) (xs : List Bool) :
    (width :: widths).splitLengths xs =
      xs.take width :: widths.splitLengths (xs.drop width) :=
  List.splitLengths_cons xs widths width

example : [2, 1].splitLengths [true, false, true] = [[true, false], [true]] := by
  decide

example :
    ([2, 1].splitLengths [10, 11, 20]).getD 1 [999] = ([10, 11, 20].drop 2).take 1 :=
  List.getD_splitLengths [10, 11, 20] [2, 1] [999] (by decide)

example :
    ((["left", "left", "right"].map fun key => if key == "left" then 1 else 2).splitLengths
        [10, 20, 21, 30, 31]).getD (["left", "left", "right"].idxOf "left") [999] = [10] :=
  List.getD_splitLengths_map (fun key : String => if key == "left" then 1 else 2)
    ["left", "left", "right"] [10, 20, 21, 30, 31] [999] (by decide)

example (length : Bool → ℕ) (names : List Bool) (xs fallback : List Bool)
    {name : Bool} (hname : name ∈ names) :
    ((names.map length).splitLengths xs).getD (names.idxOf name) fallback =
      (xs.drop ((names.map length).take (names.idxOf name)).sum).take (length name) :=
  List.getD_splitLengths_map length names xs fallback hname

example :
    ((List.replicate 3 2).splitLengths [10, 11, 20, 21, 30, 31]).getD 1 [999] =
      ([10, 11, 20, 21, 30, 31].drop (1 * 2)).take 2 :=
  List.getD_splitLengths_replicate 2 3 1 [10, 11, 20, 21, 30, 31] [999] (by decide)

example (width count i : ℕ) (xs fallback : List Bool) (hi : i < count) :
    ((List.replicate count width).splitLengths xs).getD i fallback =
      (xs.drop (i * width)).take width :=
  List.getD_splitLengths_replicate width count i xs fallback hi

example (width count : ℕ) (xs ys : List Bool)
    (hxs : xs.length = count * width) (hys : ys.length = count * width)
    (h : ∀ i < count,
      xs.extract (i * width) (i * width + width) =
        ys.extract (i * width) (i * width + width)) :
    xs = ys :=
  List.eq_of_extract_mul_eq width count xs ys hxs hys h

example : ([1, 2, 3, 4] : List Nat) = [1, 2, 3, 4] := by
  apply List.eq_of_extract_mul_eq 2 2 <;> simp

example (xs ys : List Nat) (hxs : xs.length = 4 * 0) (hys : ys.length = 4 * 0) : xs = ys := by
  apply List.eq_of_extract_mul_eq 0 4 xs ys hxs hys
  intro j hj
  simp

example (xs ys : List Nat) (hxs : xs.length = 0 * 7) (hys : ys.length = 0 * 7) : xs = ys := by
  apply List.eq_of_extract_mul_eq 7 0 xs ys hxs hys
  intro j hj
  exact (Nat.not_lt_zero j hj).elim

example : ¬ ∀ j < 2,
    ([1, 2, 3, 4] : List Nat).extract (j * 2) (j * 2 + 2) =
      [1, 2, 8, 4].extract (j * 2) (j * 2 + 2) := by
  decide

example :
    ((List.range 3).flatMap fun j => [10 * j, 10 * j + 1]).length = 3 * 2 :=
  List.length_flatMap_range 3 2 (fun j => [10 * j, 10 * j + 1]) (by simp)

example :
    ((List.range 3).flatMap fun j => [10 * j, 10 * j + 1]).extract (1 * 2) (1 * 2 + 2) =
      [10, 11] :=
  List.extract_flatMap_range 3 2 (fun j => [10 * j, 10 * j + 1]) (by simp) (by decide)

example : ∃ xs : List Nat,
    xs.length = 3 * 2 ∧
      ∀ j < 3, xs.extract (j * 2) (j * 2 + 2) = [10 * j, 10 * j + 1] :=
  List.exists_length_eq_and_extract_eq 2 3 (fun j => [10 * j, 10 * j + 1]) (by simp)

example {α : Type*} (width count : ℕ) (blocks : ℕ → List α)
    (hblocks : ∀ i < count, (blocks i).length = width) :
    ∃ xs : List α,
      xs.length = count * width ∧
        ∀ i < count, xs.extract (i * width) (i * width + width) = blocks i :=
  List.exists_length_eq_and_extract_eq width count blocks hblocks

example (width count : ℕ) (blocks : ℕ → List Bool)
    (hblocks : ∀ i < count, (blocks i).length = width) {i : ℕ} (hi : i < count) :
    ((List.range count).flatMap blocks).extract (i * width) (i * width + width) = blocks i :=
  List.extract_flatMap_range count width blocks hblocks hi
