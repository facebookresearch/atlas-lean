/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.Hadamard

@[expose] public section

/-! # Tests for the binary Hadamard code -/

namespace Cslib.CodingTheory.HadamardTests

open Cslib.CodingTheory Hadamard

/-- The encoder is the generator-matrix encoder of the linear-code API. -/
example (a : Fin 3 → ZMod 2) : encode a = LinearCode.encode (generator 3) a := rfl

example (a r : Fin 3 → ZMod 2) : encode a r = a ⬝ᵥ r := encode_apply a r

/-- The encoder is linear, sends `0` to `0`, and reads message bit `i` at `eᵢ`. -/
example (a b : Fin 3 → ZMod 2) : encode (a - b) = encode a - encode b := encode_sub a b

example : encode (0 : Fin 3 → ZMod 2) = 0 := encode_zero

example (a : Fin 3 → ZMod 2) (i : Fin 3) : encode a (Pi.single i 1) = a i :=
  encode_single_one a i

/-- The code is the set of encodings. -/
example (c : (Fin 2 → ZMod 2) → ZMod 2) : c ∈ code 2 ↔ ∃ a, encode a = c := mem_code

/-- Direct evaluation of codeword entries: the entry of the codeword of `a` at `r` is
`a ⬝ᵥ r`. -/
example : encode (![1, 1] : Fin 2 → ZMod 2) ![1, 0] = 1 := by decide

example : encode (![1, 1] : Fin 2 → ZMod 2) ![1, 1] = 0 := by decide

example : encode (![1, 0, 1] : Fin 3 → ZMod 2) ![1, 1, 1] = 0 := by decide

example : encode (![1, 0, 1] : Fin 3 → ZMod 2) ![0, 1, 1] = 1 := by decide

example : (![1, 0, 1] : Fin 3 → ZMod 2) ⬝ᵥ ![0, 1, 1] = 1 := by decide

/-- `m = 2`, by direct evaluation, independent of the general theorems: the codeword of
`(1, 0)` is `1` on exactly the two vectors with first coordinate `1`, and the codewords of
`(1, 0)` and `(0, 1)` differ exactly on `(1, 0)` and `(0, 1)`. -/
example : hammingNorm (encode (![1, 0] : Fin 2 → ZMod 2)) = 2 := by decide

example : hammingDist (encode (![1, 0] : Fin 2 → ZMod 2)) (encode ![0, 1]) = 2 := by decide

/-- The general theorems at the same instances. -/
example : hammingNorm (encode (![1, 0] : Fin 2 → ZMod 2)) = 2 ^ (2 - 1) :=
  hammingNorm_encode (by decide)

example : hammingDist (encode (![1, 0] : Fin 2 → ZMod 2)) (encode ![0, 1]) = 2 ^ (2 - 1) :=
  hammingDist_encode (by decide)

/-- Boundary `m = 1`: the codewords of `0` and `1` have length `2` and differ in exactly
`2 ^ 0 = 1` position. -/
example : hammingDist (encode (![0] : Fin 1 → ZMod 2)) (encode ![1]) = 1 := by decide

example : hammingDist (encode (![0] : Fin 1 → ZMod 2)) (encode ![1]) = 2 ^ (1 - 1) :=
  hammingDist_encode (by decide)

example : hammingNorm (encode (![1] : Fin 1 → ZMod 2)) = 2 ^ (1 - 1) :=
  hammingNorm_encode (by decide)

/-- The zero message gives the zero codeword, of weight `0`, not `2 ^ (m - 1)`. -/
example : hammingNorm (encode (0 : Fin 2 → ZMod 2)) = 0 := by decide

/-- Injectivity: distinct messages give distinct codewords. -/
example : encode (![1, 0] : Fin 2 → ZMod 2) ≠ encode ![0, 1] :=
  encode_injective.ne (by decide)

example {m : ℕ} {a b : Fin m → ZMod 2} (h : encode a = encode b) : a = b :=
  encode_injective h

/-- The parameters `[2^m, m, 2^(m-1)]` on the linear-code API, for `m ≥ 1`. -/
example : Fintype.card (Fin 3 → ZMod 2) = 8 := card_positions 3

example : Module.finrank (ZMod 2) (code 3) = 3 := finrank_code 3

example : (generator 3).rank = 3 := rank_generator 3

example : (code 3).minDist = 4 := minDist_code (by decide)

example : (code 2).minWeight = 2 := minWeight_code (by decide)

example : (code 1).minDist = 1 := minDist_code le_rfl

/-- Boundary `m = 0`: a single codeword, so the minimum distance is `⊤`. -/
example : (code 0).minDist = ⊤ := minDist_code_zero

/-- Every nonzero member of the code has weight `2 ^ (m - 1)`. -/
example : encode (![1, 1] : Fin 2 → ZMod 2) ∈ code 2 := encode_mem_code _

example {c : (Fin 3 → ZMod 2) → ZMod 2} (hc : c ∈ code 3) (hne : c ≠ 0) : hammingNorm c = 4 :=
  hammingNorm_of_mem_code hc hne

/-! The deprecated names keep their original statements, including the count form of the
distance that the QCI-39 roadmap pins. -/

section Deprecated

set_option linter.deprecated false

open MathlibExt.Combinatorics.Coding.Hadamard

example : dot (![1, 1] : Fin 2 → ZMod 2) ![1, 0] = 1 := by decide

example : hadCode (![1, 0, 1] : Fin 3 → ZMod 2) ![0, 1, 1] = 1 := by decide

example : (Finset.univ.filter
      (fun r => dot (![1, 0] : Fin 2 → ZMod 2) r = 1)).card = 2 ^ (2 - 1) :=
  hadWeight (![1, 0] : Fin 2 → ZMod 2) (by decide)

example : hammingNorm (hadCode (![1] : Fin 1 → ZMod 2)) = 2 ^ (1 - 1) :=
  hammingNorm_hadCode _ (by decide)

example {m : ℕ} (a b : Fin m → ZMod 2) (hab : a ≠ b) :
    (Finset.univ.filter (fun r => dot a r ≠ dot b r)).card = 2 ^ (m - 1) :=
  hadDist a b hab

example : hadCode (![1, 0] : Fin 2 → ZMod 2) ≠ hadCode ![0, 1] :=
  hadCode_injective.ne (by decide)

end Deprecated

end Cslib.CodingTheory.HadamardTests
