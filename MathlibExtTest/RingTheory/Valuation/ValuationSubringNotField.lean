/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.ValuationSubringNotField

@[expose] public section

/-- Consumer with the original binders: the field is explicit in the
source, and the valuation subring and its properness are as there. -/
private theorem exactSource (F : Type*) [Field F] {A : ValuationSubring F}
    (hA : A ≠ ⊤) : ¬ IsField A :=
  ValuationSubring.not_isField_of_ne_top F hA

/-- The properness hypothesis matters: the whole field, as the top
valuation subring of itself, is a field. -/
example : IsField (⊤ : ValuationSubring ℚ) := by
  refine ⟨⟨0, 1, by simp⟩, fun x y => mul_comm x y, ?_⟩
  intro a ha
  have ha0 : (a : ℚ) ≠ 0 := by
    intro h
    apply ha
    exact Subtype.ext h
  exact ⟨⟨(a : ℚ)⁻¹, ValuationSubring.mem_top _⟩,
    Subtype.ext (mul_inv_cancel₀ ha0)⟩
