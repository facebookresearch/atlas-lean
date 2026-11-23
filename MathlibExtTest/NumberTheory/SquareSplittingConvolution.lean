/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SquareSplittingConvolution

open MetaMathlibExt

example (f g : ArithmeticFunction ℂ) : squareSplitConv f g 0 = 0 :=
  (squareSplitConv f g).map_zero

-- At 4 only the divisors 1 and 4 contribute.
example (f g : ArithmeticFunction ℂ) :
    squareSplitConv f g 4 = f 1 * g 4 + f 4 * g 1 := by
  have h : squareSplitDivisors 4 = {1, 4} := by decide +kernel
  simp [squareSplitConv_apply, h]

-- The prime 2 occurs in both the squarefree and square-root parts of 72.
example : squareSplitDivisors 72 = {1, 2, 4, 8, 9, 18, 36, 72} := by decide +kernel

example {f g : ArithmeticFunction ℂ} (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) :
    squareSplitConv f g 72 = squareSplitConv f g 8 * squareSplitConv f g 9 :=
  (squareSplitConv_isMultiplicative hf hg).2 (by decide : Nat.Coprime 8 9)
