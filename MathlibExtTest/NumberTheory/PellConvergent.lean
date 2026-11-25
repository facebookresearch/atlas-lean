/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PellConvergent
import Mathlib.RingTheory.Int.Basic

/-! # Examples of Pell solutions as convergents -/

open MathlibExt.NumberTheory.PellConvergentWanted.NumberTheory

-- A nonfundamental solution for d = 2.
example : ∃ n : ℕ, (GenContFract.of (Real.sqrt 2)).convs n = 17 / 12 := by
  simpa using pell_solution_is_convergent 2
    ((Int.prime_iff_natAbs_prime (k := 2)).mpr Nat.prime_two).squarefree (by decide)
    17 12 (by decide) (by decide) (by decide)

-- A solution with denominator one for d = 3.
example : ∃ n : ℕ, (GenContFract.of (Real.sqrt 3)).convs n = 2 := by
  simpa using pell_solution_is_convergent 3
    ((Int.prime_iff_natAbs_prime (k := 3)).mpr Nat.prime_three).squarefree (by decide)
    2 1 (by decide) (by decide) (by decide)
