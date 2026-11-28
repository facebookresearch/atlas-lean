/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.SpecialLinearGroupTrace

open MetaMathlibExt.SpecialLinearGroupTrace ModularGroup

-- The diagonal entries of S * T are distinct, and inversion preserves their sum.
example : ((S * T)⁻¹).1.trace = 1 := by
  rw [← trace_eq_trace_inv (S * T)]
  decide

-- Replacing T by its inverse changes the product trace from 1 to -1.
example : (S * T⁻¹).1.trace = -1 := by
  have hS : S.1.trace = 0 := by decide
  have hST : (S * T).1.trace = 1 := by decide
  simpa only [inv_inv, hS, zero_mul, hST, zero_sub] using
    trace_mul_eq_mul_sub_trace_mul_inv S T⁻¹

-- At trace zero, the square is the negative identity.
example : S.1 ^ 2 = -1 := by
  have hS : S.1.trace = 0 := by decide
  simpa only [hS, zero_smul, zero_sub] using sq_eq_trace_smul_sub_one S
