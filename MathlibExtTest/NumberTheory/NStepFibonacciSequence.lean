/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NStepFibonacciSequence
public import Mathlib.Data.Nat.Fib.Basic

namespace MetaMathlibExt

-- 2-step: the Fibonacci numbers `0, 1, 1, 2, 3, 5, 8, 13, 21`
example : nStepFibonacci 2 2 = 1 := by simp [nStepFibonacci, Fin.sum_univ_succ]
example : nStepFibonacci 2 5 = 5 := by simp [nStepFibonacci, Fin.sum_univ_succ]
example : nStepFibonacci 2 8 = 21 := by simp [nStepFibonacci, Fin.sum_univ_succ]
example : nStepFibonacci 2 10 = Nat.fib 10 := by
  simp [nStepFibonacci, Fin.sum_univ_succ, Nat.fib_add_two]
-- 3-step: tribonacci `0, 1, 1, 2, 4, 7, 13, 24`
example : nStepFibonacci 3 4 = 4 := by simp [nStepFibonacci, Fin.sum_univ_succ]
example : nStepFibonacci 3 7 = 24 := by simp [nStepFibonacci, Fin.sum_univ_succ]
-- 4-step: tetranacci `0, 1, 1, 2, 4, 8, 15, 29`
example : nStepFibonacci 4 5 = 8 := by simp [nStepFibonacci, Fin.sum_univ_succ]
example : nStepFibonacci 4 7 = 29 := by simp [nStepFibonacci, Fin.sum_univ_succ]
-- 1-step: constant `1` after the start; 0-step: empty sum
example : nStepFibonacci 1 4 = 1 := by simp [nStepFibonacci]
example : nStepFibonacci 0 5 = 0 := by simp [nStepFibonacci]

end MetaMathlibExt
