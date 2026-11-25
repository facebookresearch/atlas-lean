/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues001

@[expose] public section

namespace MetaMathlibExt

example : tribonacci 0 = 0 := rfl
example : tribonacci 1 = 0 := rfl
example : tribonacci 2 = 1 := rfl
example : tribonacci 3 = 1 := rfl
example : tribonacci 4 = 2 := rfl
example : tribonacci 5 = 4 := rfl

example (n : ℕ) :
    tribonacci (n + 3) = tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n := rfl

-- At n = 0 the first difference vanishes; strict signs do not exclude this boundary.
example (α : ℝ) : (tribonacci 1 : ℝ) - α * tribonacci 0 = 0 := by
  simp [tribonacci]

example (α : ℝ) (hα : α ^ 3 = α ^ 2 + α + 1) :
    ¬ (∀ i < 3, 0 < (tribonacci (i + 1) : ℝ) - α * tribonacci i) ∧
      ¬ (∀ i < 3, (tribonacci (i + 1) : ℝ) - α * tribonacci i < 0) := by
  simpa only [Nat.zero_add] using tribonacci_succ_sub_mul_sign_changes (α := α) (hα := hα) (n := 0)

example (α : ℝ) (hα : α ^ 3 = α ^ 2 + α + 1) :
    ¬ (∀ i < 3, 0 < (tribonacci (1 + i + 1) : ℝ) - α * tribonacci (1 + i)) ∧
      ¬ (∀ i < 3, (tribonacci (1 + i + 1) : ℝ) - α * tribonacci (1 + i) < 0) :=
  tribonacci_succ_sub_mul_sign_changes (α := α) (hα := hα) (n := 1)

end MetaMathlibExt
