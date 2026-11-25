/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.ZMod
import MathlibExt.NumberTheory.FunctionField.MonicCount

/-! # Tests for counts of monic polynomials of bounded degree -/

open Polynomial MetaMathlibExt

-- The only monic polynomial of degree zero is the constant one.
example {F : Type*} [Field F] [Fintype F] :
    Nat.card {f : F[X] // f.Monic ∧ f.natDegree ≤ 0} = 1 := by
  have hq : (Fintype.card F : ℚ) ≠ 1 := by exact_mod_cast (Fintype.one_lt_card (α := F)).ne'
  have h := monic_count_natDegree_le (F := F) 0
  simpa [sub_ne_zero.mpr hq] using h

-- Over the field with three elements, degrees zero, one and two contribute 1 + 3 + 9.
example : Nat.card {f : (ZMod 3)[X] // f.Monic ∧ f.natDegree ≤ 2} = 13 := by
  have h := monic_count_natDegree_le (F := ZMod 3) 2
  norm_num [ZMod.card] at h
  exact_mod_cast h
