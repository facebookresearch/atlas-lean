/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.GDifferenceBases
import Mathlib.Tactic.NormNum.RealSqrt

/-! # Tests for difference representation counts and the interval lower bound -/

open MetaMathlibExt

-- Two different ordered pairs give difference 2, even though one uses a negative integer.
example : subRepCount ({-1, 0, 1, 2} : Finset ℤ) 2 = 2 := by decide

-- At multiplicity zero the empty set attains the minimum.
example (n : ℕ) : diffBasisNumber 0 n = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le (s := {k | ∃ A : Finset ℤ, A.card = k ∧
    ∀ x ∈ Finset.Icc (1 : ℤ) n, 0 ≤ subRepCount A x})
  exact ⟨∅, rfl, fun _ _ => Nat.zero_le _⟩

-- Four positive differences, each required twice, force at least four elements.
example : 4 ≤ diffBasisNumber 2 4 := by
  have h := sqrt_two_mul_le_diffBasisNumber_div_sqrt 2 4 (by decide)
  norm_num at h
  exact_mod_cast (by linarith : (4 : ℝ) ≤ diffBasisNumber 2 4)
