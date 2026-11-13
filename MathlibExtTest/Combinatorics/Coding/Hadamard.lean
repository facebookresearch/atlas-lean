/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.Hadamard
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic

@[expose] public section

open MathlibExt.Combinatorics.Coding.Hadamard

/-- Boundary check: the weight of the codeword of `(1, 0)` over
`Fin 2 → ZMod 2` is `2 ^ (2 - 1) = 2`. -/
example : (Finset.univ.filter
      (fun r => dot (![1, 0] : Fin 2 → ZMod 2) r = 1)).card = 2 ^ (2 - 1) :=
  hadWeight (![1, 0] : Fin 2 → ZMod 2) (by decide)

/-- Direct evaluation of `dot` and of codeword entries. -/
example : dot (![1, 1] : Fin 2 → ZMod 2) ![1, 0] = 1 := by decide

example : dot (![1, 1] : Fin 2 → ZMod 2) ![1, 1] = 0 := by decide

example : hadCode (![1, 0, 1] : Fin 3 → ZMod 2) ![1, 1, 1] = 0 := by decide

example : hadCode (![1, 0, 1] : Fin 3 → ZMod 2) ![0, 1, 1] = 1 := by decide

/-- Direct evaluation, independent of the general theorems: the
codeword of `(1, 0)` is `1` on exactly the two vectors with
first coordinate `1`, and the codewords of `(1, 0)` and
`(0, 1)` differ exactly on `(1, 0)` and `(0, 1)`. -/
example : hammingNorm (hadCode (![1, 0] : Fin 2 → ZMod 2)) = 2 := by decide

example : hammingDist (hadCode (![1, 0] : Fin 2 → ZMod 2)) (hadCode ![0, 1]) = 2 := by
  decide

/-- The general theorems at the same instances. -/
example : hammingNorm (hadCode (![1, 0] : Fin 2 → ZMod 2)) = 2 ^ (2 - 1) :=
  hammingNorm_hadCode _ (by decide)

example : hammingDist (hadCode (![1, 0] : Fin 2 → ZMod 2)) (hadCode ![0, 1]) = 2 ^ (2 - 1) :=
  hadDist _ _ (by decide)

/-- The distance theorem is the raw count over `dot`: unfolding
`hammingDist` and `hadCode` recovers it. -/
example {m : ℕ} (a b : Fin m → ZMod 2) (hab : a ≠ b) :
    (Finset.univ.filter (fun r => dot a r ≠ dot b r)).card = 2 ^ (m - 1) :=
  hadDist a b hab

/-- Boundary `m = 1`: the codewords of `0` and `1` have length
`2` and differ in exactly `2 ^ 0 = 1` position. -/
example : hammingDist (hadCode (![0] : Fin 1 → ZMod 2)) (hadCode ![1]) = 1 := by decide

example : hammingDist (hadCode (![0] : Fin 1 → ZMod 2)) (hadCode ![1]) = 2 ^ (1 - 1) :=
  hadDist _ _ (by decide)

example : hammingNorm (hadCode (![1] : Fin 1 → ZMod 2)) = 2 ^ (1 - 1) :=
  hammingNorm_hadCode _ (by decide)

/-- Injectivity: distinct messages give distinct codewords. -/
example : hadCode (![1, 0] : Fin 2 → ZMod 2) ≠ hadCode ![0, 1] :=
  hadCode_injective.ne (by decide)

example {m : ℕ} {a b : Fin m → ZMod 2} (h : hadCode a = hadCode b) : a = b :=
  hadCode_injective h
