/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FLT.Five
import Mathlib.Tactic.NormNum.Basic

/-! # Tests for Fermat's Last Theorem for exponent 5 -/

@[expose] public section

-- `exactSource` consumer with the original statement.
private theorem exactSource : FermatLastTheoremFor 5 :=
  fermatLastTheoremFive

/-- The statement with its binders unfolded. -/
example (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ 5 + b ^ 5 ≠ c ^ 5 :=
  fermatLastTheoremFive a b c ha hb hc

/-- The integer form. -/
example : FermatLastTheoremWith ℤ 5 :=
  fermatLastTheoremFor_iff_int.mp fermatLastTheoremFive

/-- Boundary: the nonzero hypotheses matter, since `0 ^ 5 + 1 ^ 5 = 1 ^ 5`. -/
example : (0 : ℕ) ^ 5 + 1 ^ 5 = 1 ^ 5 := by norm_num

/-- Boundary: the exponent matters, since `3 ^ 2 + 4 ^ 2 = 5 ^ 2`. -/
example : ¬ FermatLastTheoremFor 2 := fun h => h 3 4 5 (by norm_num) (by norm_num)
  (by norm_num) (by norm_num)
