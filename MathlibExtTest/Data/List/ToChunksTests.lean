/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Data.List.ToChunks
import all Batteries.Data.List.Basic

@[expose] public section

example (n : Nat) (xs : List Nat) : (xs.toChunks n).flatten = xs := List.flatten_toChunks n xs
example : (([] : List Nat).toChunks 5).length = 0 := by decide
example : ([1, 2, 3, 4, 5, 6].toChunks 5).length = 2 := by decide
example : ([1, 2, 3].toChunks 0).flatten = [1, 2, 3] := by decide

example (xs chunk : List Nat) (hchunk : chunk ∈ xs.toChunks 5) : chunk.length ≤ 5 :=
  List.length_le_of_mem_toChunks 5 xs (by decide) chunk hchunk

example (xs chunk : List Nat) (hchunk : chunk ∈ (xs.toChunks 5).dropLast) : chunk.length = 5 :=
  List.length_eq_of_mem_dropLast_toChunks 5 xs chunk hchunk

example (xs chunk : List Nat) (hchunk : chunk ∈ xs.toChunks 0) : chunk ≠ [] :=
  List.ne_nil_of_mem_toChunks 0 xs chunk hchunk
