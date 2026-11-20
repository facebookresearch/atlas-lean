/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DivideAndConquer.AlgebraicCostAudit
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

universe u

namespace Cslib.Algorithms.Lean.AlgebraicCostAuditTests

open Cslib.Algorithms.Lean.TimeM Cslib.Algorithms.Lean.Matrix
open Cslib.Algorithms.Lean.AlgebraicCostAudit

theorem karatsuba_concrete_value :
    (karatsuba 10 2 12 34).ret = 408 := by
  rw [karatsuba_ret]

def matA2 : Vector (Vector Int (2 ^ 1)) (2 ^ 1) :=
  Vector.ofFn fun i => Vector.ofFn fun j => 2 * (i.val : Int) + (j.val : Int) + 1

def matB2 : Vector (Vector Int (2 ^ 1)) (2 ^ 1) :=
  Vector.ofFn fun i => Vector.ofFn fun j => 2 * (i.val : Int) + (j.val : Int) + 5

theorem strassen_2x2_concrete :
    (Matrix.of fun i j =>
      (((strassenMatrixAccumulate 1 matA2 matB2 0).ret.get i).get j)) =
      Matrix.of fun i j => (4 * (i.val : Int) * (j.val : Int) +
        24 * (i.val : Int) + 3 * (j.val : Int) + 19) := by
  have h := strassen_value 1 matA2 matB2
  rw [h]
  decide

-- T3 covered upstream, no duplicate needed:
-- CSLibExtTest/Algorithms/Lean/Fourier/FFTProofInterfaceTests.lean checks
-- ifft_fft_stdAddChar_neg_one, fft_ifft_stdAddChar_neg_one, ifft_fft_stdAddChar_one,
-- fft_ifft_stdAddChar_one; FFTExactComplexTests.lean in the same dir covers both signs.

theorem strassen_S1_k0 {R : Type u} [Zero R] [Add R] [Sub R] [Mul R]
    (A B C : Vector (Vector R (2 ^ 0)) (2 ^ 0)) :
    ((strassenMatrixAccumulate 0 A B C).time.1 : ℝ) = 1 := by
  have h := strassen_mul_count 0 A B C
  rw [h, show ((2 ^ 0 : ℕ) : ℝ) = 1 from by norm_num]
  exact Real.one_rpow _

theorem strassen_S1_k1 {R : Type u} [Zero R] [Add R] [Sub R] [Mul R]
    (A B C : Vector (Vector R (2 ^ 1)) (2 ^ 1)) :
    ((strassenMatrixAccumulate 1 A B C).time.1 : ℝ) = 7 := by
  have h := strassen_mul_count 1 A B C
  rw [h, show ((2 ^ 1 : ℕ) : ℝ) = 2 from by norm_num]
  exact Real.rpow_logb (b := 2) (x := 7) (by norm_num) (by norm_num) (by norm_num)

theorem strassen_S2_k0 {R : Type u} [Zero R] [Add R] [Sub R] [Mul R]
    (A B C : Vector (Vector R (2 ^ 0)) (2 ^ 0)) :
    ((((strassenMatrixAccumulate 0 A B C).time.1 +
      (strassenMatrixAccumulate 0 A B C).time.2 : ℕ)) : ℝ) ≤ 28 / 3 := by
  have h := strassen_ops_le 0 A B C
  rw [show ((2 ^ 0 : ℕ) : ℝ) = 1 from by norm_num, Real.one_rpow, mul_one] at h
  exact h

theorem strassen_S2_k1 {R : Type u} [Zero R] [Add R] [Sub R] [Mul R]
    (A B C : Vector (Vector R (2 ^ 1)) (2 ^ 1)) :
    ((((strassenMatrixAccumulate 1 A B C).time.1 +
      (strassenMatrixAccumulate 1 A B C).time.2 : ℕ)) : ℝ) ≤
      (28 / 3) * 7 := by
  have h := strassen_ops_le 1 A B C
  rw [show ((2 ^ 1 : ℕ) : ℝ) = 2 from by norm_num,
    Real.rpow_logb (b := 2) (x := 7) (by norm_num) (by norm_num) (by norm_num)] at h
  exact h

end Cslib.Algorithms.Lean.AlgebraicCostAuditTests
