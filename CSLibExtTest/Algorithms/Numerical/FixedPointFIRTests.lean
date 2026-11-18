/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Numerical.FixedPointFIR
public meta import CSLibExt.Algorithms.Numerical.FixedPointFIR
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
