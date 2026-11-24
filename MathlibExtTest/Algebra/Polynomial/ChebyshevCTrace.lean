/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.ChebyshevCTrace

/-! # Tests for the monic Chebyshev trace formula -/

open Polynomial MetaMathlibExt

-- The zeroth power has trace two, the initial value of the monic normalization.
example : Matrix.trace ((!![X, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ[X]) ^ 0) = 2 := by
  rw [← chebyshevC_eq_trace_pow]
  simp

-- The first power reached by the recurrence has trace X² - 2.
example : Matrix.trace ((!![X, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ[X]) ^ 2) = X ^ 2 - 2 := by
  rw [← chebyshevC_eq_trace_pow]
  exact Chebyshev.C_two ℤ
