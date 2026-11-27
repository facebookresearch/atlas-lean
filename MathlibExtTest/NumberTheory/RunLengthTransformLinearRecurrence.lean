/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RunLengthTransformLinearRecurrence
import Mathlib.LinearAlgebra.Matrix.Notation

open Matrix MetaMathlibExt

-- The empty digit list gives the identity even for a one-dimensional representation.
example (a : ℤ) : runLengthTransform (fun k => a ^ k) 0 = 1 := by
  simpa using runLengthTransform_linearRecurrence_eq_linearRep 0 (fun _ => a) (fun k => a ^ k)
    (pow_zero a) (fun m _ => by simp [pow_succ']) 0

-- In 11001110 the runs of lengths two and three contribute 5 and 7 for S(k) = 2k + 1.
example : runLengthTransform (fun k => 2 * (k : ℤ) + 1) 206 = 35 := by
  rw [runLengthTransform_linearRecurrence_eq_linearRep 1 ![2, -1] _ (by decide)
    (fun m hm => by
      simp [Fin.sum_univ_two, Nat.cast_sub hm]
      omega)]
  decide
