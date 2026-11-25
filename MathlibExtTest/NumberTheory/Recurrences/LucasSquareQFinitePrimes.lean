/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.Recurrences.LucasSquareQFinitePrimes

open MetaMathlibExt

-- For P = 5 and Q = 4, the finite set of prime indices contains 2.
example : {n : ℕ | (lucasU ⟨5, 4, by decide⟩ n).natAbs.Prime}.Finite ∧
    (lucasU ⟨5, 4, by decide⟩ 2).natAbs.Prime := by
  exact ⟨lucasU_square_q_finite_primes (hQ := by decide) (hP := by decide)
    (hD := by decide) (hsq := ⟨-2, by decide⟩), by decide⟩

-- Check the first odd and even indices beyond 2 for parameters with a common divisor.
example : ¬ (lucasU ⟨6, 4, by decide⟩ 3).natAbs.Prime ∧
    ¬ (lucasU ⟨6, 4, by decide⟩ 4).natAbs.Prime := by norm_num [lucasU]
