/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CongruentPairQuadraticSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Finset MetaMathlibExt

-- With l = 1 the cotangent sum is empty.
example : (∑ a ∈ Icc 1 4, ∑ b ∈ (Icc 1 4).filter (fun b ↦ b ≡ a [MOD 5]),
    ((a : ℝ) / 5 - 1 / 2) * ((b : ℝ) / 5 - 1 / 2)) = 1 / 5 := by
  have h := congruentPairQuadraticSum_eq_sub_dedekindSum (p := 5) (l := 1)
    (by decide) (by decide) (by decide)
  norm_num at h
  exact h

-- For p = 2 the only centered residue is zero. The cotangent sum for l = 7 is nonzero.
example : (∑ a ∈ Icc 1 (6 : ℕ),
    Real.cot (Real.pi * a / 7) * Real.cot (Real.pi * a * 2 / 7)) = 2 := by
  have h := congruentPairQuadraticSum_eq_sub_dedekindSum (p := 2) (l := 7)
    (by decide) (by decide) (by decide)
  norm_num at h
  linarith
