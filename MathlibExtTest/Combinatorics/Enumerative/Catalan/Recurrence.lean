/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.Catalan.Recurrence

open MetaMathlibExt

example (n : ℕ) :
    (catalan (n + 1) : ℚ) = 2 * (2 * (n : ℚ) + 1) / (n + 2) * catalan n :=
  cast_catalan_succ_eq n

example (n : ℕ) :
    (catalan (n + 1) : ℂ) = 2 * (2 * (n : ℂ) + 1) / (n + 2) * catalan n :=
  cast_catalan_succ_eq n

example : catalan 3 = 5 := by
  have h : 4 * catalan 3 = 20 := by
    simpa [catalan_two] using add_two_mul_catalan_succ 2
  omega
