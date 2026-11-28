/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.BilinearRecursionSize

/-!
# Tests for recursive bilinear circuit gate counts
-/

set_option autoImplicit false

universe u

namespace Cslib.Complexity.Algebraic

#check @blockEncoder_size
#check @blockDecoder_size
#check @recursiveCircuit_size_zero
#check @recursiveCircuit_size_succ
#check @recursiveCircuit_size_closed
#check @recursiveCircuit_size_le

example {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) :
    (recursiveCircuit terms 1).size = terms.length + 6 * terms.length * q ^ 2 := by
  simpa using recursiveCircuit_size_succ terms 0

example {F : Type u} [Field F]
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)))
    (hlen : terms.length ≤ 7) (k : ℕ) :
    (recursiveCircuit terms k).size + 168 * 4 ^ k ≤ 169 * 7 ^ k := by
  have h42 : (2 : ℕ) ^ (2 * k) = 4 ^ k := by
    rw [pow_mul]
    norm_num
  have h := recursiveCircuit_size_le terms hlen (show 2 ^ 2 < 7 by decide) k
  rw [h42] at h
  norm_num at h
  exact h

example {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) :
    ((terms.length : ℤ) - (q : ℤ) ^ 2) * ((recursiveCircuit terms 0).size : ℤ) +
        6 * terms.length * (q : ℤ) ^ 2 * (q : ℤ) ^ (2 * 0) =
      ((terms.length : ℤ) - (q : ℤ) ^ 2 + 6 * terms.length * (q : ℤ) ^ 2) *
        (terms.length : ℤ) ^ 0 :=
  recursiveCircuit_size_closed terms 0

#check @IsMatrixMultiplication.exists_size_le_of_le

example {F : Type u} [Field F] (c : MatrixArithmeticCircuit F 4 4 4)
    (hc : IsMatrixMultiplication c) :
    ∃ c' : MatrixArithmeticCircuit F 3 3 3, IsMatrixMultiplication c' ∧
      c'.size ≤ c.size :=
  IsMatrixMultiplication.exists_size_le_of_le (by norm_num) hc

#check @recursiveCircuit_size_le_rpow

example {F : Type u} [Field F]
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)))
    (hlen : terms.length ≤ 7) (k : ℕ) :
    ((recursiveCircuit terms k).size : ℝ) ≤
      (1 + 6 * 7 * 2 ^ 2) * ((2 ^ k : ℕ) : ℝ) ^ Real.logb 2 7 :=
  recursiveCircuit_size_le_rpow terms (by norm_num) hlen (by decide) k

end Cslib.Complexity.Algebraic
