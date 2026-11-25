/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomialModTwoRunLength
import Mathlib.LinearAlgebra.Matrix.Notation

open Matrix MetaMathlibExt

-- With a single coefficient, the companion matrix gives the geometric sequence.
example (a : ℤ) (n : ℕ) :
    a ^ n = ((Matrix.of fun _ _ : Fin 1 => a) ^ n *ᵥ fun _ => 1) 0 := by
  have h := linearRecurrence_eq_companion_pow 0 (fun _ => a) (fun k => a ^ k)
    (pow_zero a) (fun m _ => by simp [pow_succ']) n
  simpa [Fin.fin_one_eq_zero] using h

-- Distinct, signed coefficients check the order of the last row, with S(1) = 3.
example (n : ℕ) : 2 * (n : ℤ) + 1 = ((!![0, 1; -1, 2] : Matrix _ _ ℤ) ^ n *ᵥ ![1, 3]) 0 := by
  have h := linearRecurrence_eq_companion_pow 1 ![2, -1] (fun k => 2 * (k : ℤ) + 1)
    (by decide) (fun m hm => by
      simp [Fin.sum_univ_two, Nat.cast_sub hm]
      omega) n
  rw [single_one_dotProduct] at h
  convert h using 1
  congr 3 <;> decide

-- A nonbinary digit ends the accumulated run, and the final run is still emitted.
example : bitRunLengths [1, 2, 0, 1] 2 = [3, 1] := by decide

-- Reading 11011 from the low end gives two separate runs of length two.
example (S : ℕ → ℤ) : runLengthTransform S 27 = S 2 * S 2 := by
  have h : binaryRunLengths 27 = [2, 2] := by decide
  simp [runLengthTransform, h]
