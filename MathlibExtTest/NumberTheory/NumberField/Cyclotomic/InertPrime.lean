/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Cyclotomic.InertPrime
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

@[expose] public section

open scoped NumberField

namespace MathlibExtTest.NumberTheory.CyclotomicInertPrime

/-- `2` has order `4 = 5 - 1` modulo `5`. -/
example : orderOf ((2 : ℕ) : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hmpos
  interval_cases m <;> decide

/-- `2` is inert in `ℚ(ζ₅)`: the quotient by `(2)` is a field. -/
example : IsField (𝓞 (CyclotomicField 5 ℚ) ⧸
    Ideal.span {(2 : 𝓞 (CyclotomicField 5 ℚ))}) := by
  have hord : orderOf ((2 : ℕ) : ZMod 5) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hmpos
    interval_cases m <;> decide
  have _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have _ : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  refine (IsCyclotomicExtension.Rat.isField_quotient_span_natCast_iff_orderOf_eq
    (K := CyclotomicField 5 ℚ) (p := 2) (ℓ := 5) (by decide)).mpr ?_
  rw [hord]

/-- `3` has order `4 = 5 - 1` modulo `5`, so it is inert in `ℚ(ζ₅)` too. -/
example : IsField (𝓞 (CyclotomicField 5 ℚ) ⧸
    Ideal.span {(3 : 𝓞 (CyclotomicField 5 ℚ))}) := by
  have hord : orderOf ((3 : ℕ) : ZMod 5) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hmpos
    interval_cases m <;> decide
  have _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have _ : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  refine (IsCyclotomicExtension.Rat.isField_quotient_span_natCast_iff_orderOf_eq
    (K := CyclotomicField 5 ℚ) (p := 3) (ℓ := 5) (by decide)).mpr ?_
  rw [hord]

/-- `2` has order `3 ≠ 7 - 1` modulo `7`, so it is not inert in `ℚ(ζ₇)`. -/
example : ¬ IsField (𝓞 (CyclotomicField 7 ℚ) ⧸
    Ideal.span {(2 : 𝓞 (CyclotomicField 7 ℚ))}) := by
  have hord : orderOf ((2 : ℕ) : ZMod 7) = 3 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hmpos
    interval_cases m <;> decide
  have _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have _ : IsCyclotomicExtension {7} ℚ (CyclotomicField 7 ℚ) :=
    CyclotomicField.isCyclotomicExtension 7 ℚ
  intro hfield
  have h2 := (IsCyclotomicExtension.Rat.isField_quotient_span_natCast_iff_orderOf_eq
    (K := CyclotomicField 7 ℚ) (p := 2) (ℓ := 7) (by decide)).mp hfield
  rw [hord] at h2
  norm_num at h2

end MathlibExtTest.NumberTheory.CyclotomicInertPrime
