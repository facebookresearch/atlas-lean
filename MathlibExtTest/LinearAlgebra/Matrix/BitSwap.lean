/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.LinearAlgebra.Matrix.BitSwap

open Matrix Finset

-- The vector is unnormalized; its two nonzero entries have opposite signs.
example : bitSinglet (false, true) = 1 ∧ bitSinglet (true, false) = -1 ∧
    bitSinglet (false, false) = 0 ∧ bitSinglet (true, true) = 0 := by decide

-- Zero bits: the unique matrix entry is one.
example (p q : (Fin 0 → Bool) × (Fin 0 → Bool)) : bitSwapPiece 0 0 p q = 1 := by
  simp [bitSwapPiece]

-- Every one-bit matrix entry: the zeroth piece is the identity.
example : ∀ a b u v : Bool,
    bitSwapPiece 1 0 (fun _ => a, fun _ => b) (fun _ => u, fun _ => v) =
      (if a = u ∧ b = v then 1 else 0 : ℤ) := by
  decide

-- All 256 two-bit entries, checked independently of the decomposition theorem.
example : ∀ a b c d u v w z : Bool,
    ∑ i ∈ range 3, bitSwapPiece 2 i
      (fun k => if k = 0 then a else b, fun k => if k = 0 then c else d)
      (fun k => if k = 0 then u else v, fun k => if k = 0 then w else z) =
        (if a = w ∧ b = z ∧ c = u ∧ d = v then 1 else 0 : ℤ) := by
  decide

example (x y u v : Fin 2 → Bool) :
    ∑ i ∈ range 3, bitSwapPiece 2 i (x, y) (u, v) =
      (Equiv.prodComm (Fin 2 → Bool) (Fin 2 → Bool)).toPEquiv.toMatrix (x, y) (u, v) :=
  sum_bitSwapPiece 2 (x, y) (u, v)

example : bitSwapPiece 2 3 = 0 := bitSwapPiece_eq_zero_of_lt (by decide)

example (p q : (Fin 2 → Bool) × (Fin 2 → Bool)) : |bitSwapPiece 2 1 p q| ≤ 2 := by
  simpa [Nat.choose] using abs_bitSwapPiece_le_choose 2 1 p q

#print axioms Matrix.bitSwap_eq_one_sub_vecMulVec
#print axioms Matrix.sum_bitSwapPiece
#print axioms Matrix.abs_bitSwapPiece_le_choose
#print axioms Matrix.abs_bitSwapPiece_le_two_pow
