/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.SpecialLinearGroupTrace

open MetaMathlibExt ModularGroup

-- The diagonal entries of S * T are distinct, and inversion preserves their sum.
example : ((S * T)⁻¹).1.trace = 1 := by
  rw [← (specialLinearGroup_two_trace_identities (S * T) T).1]
  decide

-- Replacing T by its inverse changes the product trace from 1 to -1.
example : (S * T⁻¹).1.trace = -1 := by
  have hS : S.1.trace = 0 := by decide
  have hST : (S * T).1.trace = 1 := by decide
  simpa only [inv_inv, hS, zero_mul, hST, zero_sub] using
    (specialLinearGroup_two_trace_identities S T⁻¹).2.1

-- At trace zero, the square is the negative identity.
example : S.1 ^ 2 = -1 := by
  have hS : S.1.trace = 0 := by decide
  simpa only [hS, zero_smul, zero_sub] using (specialLinearGroup_two_trace_identities S T).2.2
