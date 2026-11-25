/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.AbsoluteValue.FiniteField

import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open AbsoluteValue

variable {K : Type*} [Field K]

/-- Abstract positive-characteristic case is nonarchimedean. -/
public theorem test_charP_abstract (p : ℕ) [CharP K p] [NeZero p]
    (v : AbsoluteValue K ℝ) : IsNonarchimedean v :=
  isNonarchimedean_of_charP v

/-- Abstract finite pointwise triviality on nonzero elements. -/
public theorem test_finite_abstract [Finite K] (v : AbsoluteValue K ℝ)
    {x : K} (hx : x ≠ 0) : v x = 1 :=
  eq_one_of_ne_zero_of_finite v hx

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Concrete positive-characteristic case on `ZMod 5`. -/
public theorem test_charP_zmod5 (v : AbsoluteValue (ZMod 5) ℝ) :
    IsNonarchimedean v :=
  isNonarchimedean_of_charP (K := ZMod 5) (p := 5) v

/-- Concrete finite nonzero evaluation at `2 : ZMod 5`. -/
public theorem test_finite_zmod5_two (v : AbsoluteValue (ZMod 5) ℝ)
    (h : (2 : ZMod 5) ≠ 0) : v 2 = 1 :=
  eq_one_of_ne_zero_of_finite (K := ZMod 5) (x := (2 : ZMod 5)) v h

/-- Zero always maps to zero. -/
public theorem test_zero_eval (v : AbsoluteValue (ZMod 5) ℝ) : v 0 = 0 :=
  v.map_zero

end
