/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.PuncturedDiscLaurent

/-!
# Tests for `MathlibExt.Analysis.Complex.PuncturedDiscLaurent`
-/

set_option autoImplicit false

@[expose] public section

#check @WLight.IsPuncturedDiscLaurent
#check @WLight.laurentSum
#check @WLight.laurentConv
#check @WLight.laurentConv_eq_zero_of_lt
#check @WLight.map_laurentConv
#check @WLight.IsPuncturedDiscLaurent.summable_norm
#check @WLight.laurentSum_mul
#check @WLight.IsPuncturedDiscLaurent.laurentConv
#check @WLight.IsPuncturedDiscLaurent.add
#check @WLight.IsPuncturedDiscLaurent.neg
#check @WLight.isPuncturedDiscLaurent_single
#check @WLight.laurentSum_add
#check @WLight.laurentSum_neg
#check @WLight.IsPuncturedDiscLaurent.eq_zero_of_laurentSum_eq_zero
#check @WLight.IsPuncturedDiscLaurent.ext_of_laurentSum_eq

#print axioms WLight.laurentConv_eq_zero_of_lt
#print axioms WLight.map_laurentConv
#print axioms WLight.IsPuncturedDiscLaurent.summable_norm
#print axioms WLight.laurentSum_mul
#print axioms WLight.IsPuncturedDiscLaurent.laurentConv
#print axioms WLight.IsPuncturedDiscLaurent.add
#print axioms WLight.IsPuncturedDiscLaurent.neg
#print axioms WLight.isPuncturedDiscLaurent_single
#print axioms WLight.laurentSum_add
#print axioms WLight.laurentSum_neg
#print axioms WLight.IsPuncturedDiscLaurent.eq_zero_of_laurentSum_eq_zero
#print axioms WLight.IsPuncturedDiscLaurent.ext_of_laurentSum_eq

/-- The product of the monomials `w⁻¹` and `2 w³` is the sum of their convolution. -/
example {w : ℂ} (hw0 : w ≠ 0) (hw1 : ‖w‖ < 1) :
    w ^ (-1 : ℤ) * (2 * w ^ (3 : ℤ)) = WLight.laurentSum
      (WLight.laurentConv (fun n => if n = -1 then (1 : ℂ) else 0)
        (fun n => if n = 3 then (2 : ℂ) else 0)) w := by
  obtain ⟨h1, s1⟩ := WLight.isPuncturedDiscLaurent_single (-1) (1 : ℂ)
  obtain ⟨h2, s2⟩ := WLight.isPuncturedDiscLaurent_single 3 (2 : ℂ)
  rw [← WLight.laurentSum_mul h1 h2 hw0 hw1, s1, s2, one_mul]

/-- A monomial `c wⁿ` vanishing on the punctured unit disc has `c = 0`. -/
example (c : ℂ) (n₀ : ℤ) (h : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → c * w ^ n₀ = 0) : c = 0 := by
  obtain ⟨hL, hS⟩ := WLight.isPuncturedDiscLaurent_single n₀ c
  have := hL.eq_zero_of_laurentSum_eq_zero fun w hw0 hw1 => by rw [hS]; exact h w hw0 hw1
  simpa using congrFun this n₀
