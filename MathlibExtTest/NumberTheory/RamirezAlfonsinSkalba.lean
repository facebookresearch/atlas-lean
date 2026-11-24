/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RamirezAlfonsinSkalba

/-! # Tests for two representations by coprime generators -/

open MetaMathlibExt

-- The representations 2 * 3 + 3 * 0 and 2 * 0 + 3 * 2 give a negative y-difference.
example : (2 : ℤ) ∣ -2 ∧ (3 : ℤ) ∣ 3 :=
  twoGenerator_dvd_sub_of_eq (c := 2) (d := 3) (x := 3) (y := 0) (x' := 0) (y' := 2)
    (by decide) rfl

-- With generators 0 and 1 the first coordinate is unrestricted.
example (x x' y : ℕ) : (0 : ℤ) ∣ (y : ℤ) - y ∧ (1 : ℤ) ∣ (x : ℤ) - x' :=
  twoGenerator_dvd_sub_of_eq (c := 0) (d := 1) (x := x) (x' := x') (y := y) (y' := y)
    (by decide) (by simp)
