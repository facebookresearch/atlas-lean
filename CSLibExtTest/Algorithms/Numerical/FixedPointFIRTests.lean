/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Numerical.FixedPointFIR
public meta import CSLibExt.Algorithms.Numerical.FixedPointFIR
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-! # Fixed-point FIR filter examples -/

open CSLibExt.Algorithms.Numerical.FixedPointFIR

example : roundHalfUpShift 1 3 = 2 := by decide
example : roundHalfUpShift 1 (-3) = -1 := by decide
example : roundHalfUpShift 2 6 = 2 := by decide

example : saturate (-8) 7 100 = 7 := by decide
example : saturate (-8) 7 (-100) = -8 := by decide
example : saturate (-8) 7 3 = 3 := by decide

example : firCode 1 (-8) 7 (fun _ : Fin 2 => (1 : ℤ)) (fun _ : Fin 2 => (1 : ℤ)) = 2 := by
  decide

example : firOverflow 1 (-8) 7 (fun _ : Fin 2 => (1 : ℤ)) (fun _ : Fin 2 => (1 : ℤ)) = false := by
  decide

example : decode 1 (firCode 1 (-8) 7 (fun _ : Fin 2 => (1 : ℤ))
    (fun _ : Fin 2 => (1 : ℤ))) = 1 := by
  have h : firCode 1 (-8) 7 (fun _ : Fin 2 => (1 : ℤ)) (fun _ : Fin 2 => (1 : ℤ)) = 2 := by
    decide
  rw [h]
  norm_num [decode]

/-! ## Saturation and overflow -/

-- The running sum `5 + 5` leaves the range: the code clamps to the top.
example : firCode 0 (-8) 7 ![5, 5] ![1, 1] = 7 := by decide
example : firOverflow 0 (-8) 7 ![5, 5] ![1, 1] = true := by decide

-- The third step returns into range; the code continues from the clamped
-- value and the flag stays set.
example : firCode 0 (-8) 7 ![5, 5, -5] ![1, 1, 1] = 2 := by decide
example : firOverflow 0 (-8) 7 ![5, 5, -5] ![1, 1, 1] = true := by decide

-- Negative saturation clamps to the bottom.
example : firCode 0 (-8) 7 ![-5, -5] ![1, 1] = -8 := by decide
example : firOverflow 0 (-8) 7 ![-5, -5] ![1, 1] = true := by decide

-- A product out of range is flagged even when the running sum is not.
example : firCode 0 (-8) 7 ![-1, 3] ![6, 3] = 3 := by decide
example : firOverflow 0 (-8) 7 ![-1, 3] ![6, 3] = true := by decide

-- The no-overflow refinement equation fails on the saturating trace:
-- the decoded code is 7, while the fold with the actual decoding and
-- rounding errors and zero accumulation error gives 10.
example : decode 0 (firCode 0 (-8) 7 ![5, 5] ![1, 1])
    ≠ MathlibExt.Analysis.Numerical.OrderedDotProductError.outputPerturbed 2
      (fun _ => 0) (fun k => decode 0 (![5, 5] k) - 0)
      (fun _ => 0) (fun k => decode 0 (![1, 1] k) - 0)
      (fun k => decode 0 (roundHalfUpShift 0 (![5, 5] k * ![1, 1] k))
        - decode 0 (![5, 5] k) * decode 0 (![1, 1] k))
      (fun _ => 0) := by
  have h : firCode 0 (-8) 7 ![5, 5] ![1, 1] = 7 := by decide
  rw [h]
  norm_num [decode, roundHalfUpShift,
    MathlibExt.Analysis.Numerical.OrderedDotProductError.outputPerturbed,
    MathlibExt.Analysis.Numerical.OrderedDotProductError.accumulator,
    MathlibExt.Analysis.Numerical.OrderedDotProductError.extend,
    MathlibExt.Analysis.Numerical.OrderedDotProductError.productPerturbed,
    MathlibExt.Analysis.Numerical.OrderedDotProductError.coeffPerturbed,
    MathlibExt.Analysis.Numerical.OrderedDotProductError.inputPerturbed]

-- Overflow only removes the guarantee: on the product fixture above,
-- only the product `9` leaves the range, both running sums fit, and both
-- sides equal 3.
example : decode 0 (firCode 0 (-8) 7 ![-1, 3] ![6, 3])
    = MathlibExt.Analysis.Numerical.OrderedDotProductError.outputPerturbed 2
      (fun _ => 0) (fun k => decode 0 (![-1, 3] k) - 0)
      (fun _ => 0) (fun k => decode 0 (![6, 3] k) - 0)
      (fun k => decode 0 (roundHalfUpShift 0 (![-1, 3] k * ![6, 3] k))
        - decode 0 (![-1, 3] k) * decode 0 (![6, 3] k))
      (fun _ => 0) := by
  have h : firCode 0 (-8) 7 ![-1, 3] ![6, 3] = 3 := by decide
  rw [h]
  norm_num [decode, roundHalfUpShift,
    MathlibExt.Analysis.Numerical.OrderedDotProductError.outputPerturbed,
    MathlibExt.Analysis.Numerical.OrderedDotProductError.accumulator,
    MathlibExt.Analysis.Numerical.OrderedDotProductError.extend,
    MathlibExt.Analysis.Numerical.OrderedDotProductError.productPerturbed,
    MathlibExt.Analysis.Numerical.OrderedDotProductError.coeffPerturbed,
    MathlibExt.Analysis.Numerical.OrderedDotProductError.inputPerturbed]
