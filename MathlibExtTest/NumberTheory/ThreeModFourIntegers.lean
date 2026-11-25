/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ThreeModFourIntegers

open Filter Asymptotics

namespace MetaMathlibExtTest.ThreeModFourIntegers

/-! The counting function counts `n = 1` and every product of primes `≡ 3 (mod 4)`. -/

example : ((Finset.Icc 1 10).filter fun n => ∀ q ∈ n.primeFactors, q % 4 = 3).card = 4 := by
  decide +kernel

-- `21 = 3 · 7` is counted; `15 = 3 · 5` and `18 = 2 · 3 ^ 2` are not.
example : ((Finset.Icc 1 25).filter fun n => ∀ q ∈ n.primeFactors, q % 4 = 3) =
    {1, 3, 7, 9, 11, 19, 21, 23} := by
  decide +kernel

/-! Applications of the asymptotic formula. -/

/-- The hypothesis forces `C ≠ 0`: otherwise the main term vanishes while `g(x) ≥ 1`. -/
private theorem const_ne_zero {C : ℝ}
    (hC : Tendsto (fun x : ℕ => √(Real.log x) *
      ∏ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1), (1 - 1 / (q : ℝ)))
      atTop (nhds C)) :
    C ≠ 0 := by
  rintro rfl
  have h := MetaMathlibExt.isEquivalent_card_primeFactors_three_mod_four hC
  have h0 : (fun x : ℕ => √(Real.exp Real.eulerMascheroniConstant / Real.pi) * 0 / 2 * x /
      √(Real.log x)) = 0 := by
    funext x
    simp
  rw [h0, isEquivalent_zero_iff_eventually_zero] at h
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hmem : 1 ∈ (Finset.Icc 1 (N + 1)).filter fun n => ∀ q ∈ n.primeFactors, q % 4 = 3 := by
    simp
  have hpos := Finset.card_pos.mpr ⟨1, hmem⟩
  have h1 := hN (N + 1) (Nat.le_succ N)
  simp only [Pi.zero_apply, Nat.cast_eq_zero] at h1
  omega

/-- The asymptotic formula in ratio form: `g(x)` divided by the main term tends to `1`. -/
example {C : ℝ}
    (hC : Tendsto (fun x : ℕ => √(Real.log x) *
      ∏ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1), (1 - 1 / (q : ℝ)))
      atTop (nhds C)) :
    Tendsto (fun x : ℕ =>
      (((Finset.Icc 1 x).filter fun n => ∀ q ∈ n.primeFactors, q % 4 = 3).card : ℝ) /
        (√(Real.exp Real.eulerMascheroniConstant / Real.pi) * C / 2 * x / √(Real.log x)))
      atTop (nhds 1) := by
  have hK : √(Real.exp Real.eulerMascheroniConstant / Real.pi) * C / 2 ≠ 0 := by
    have hpos : 0 < √(Real.exp Real.eulerMascheroniConstant / Real.pi) :=
      Real.sqrt_pos.mpr (div_pos (Real.exp_pos _) Real.pi_pos)
    exact div_ne_zero (mul_ne_zero hpos.ne' (const_ne_zero hC)) two_ne_zero
  have hv : ∀ᶠ x : ℕ in atTop,
      √(Real.exp Real.eulerMascheroniConstant / Real.pi) * C / 2 * x / √(Real.log x) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hx1 : (1 : ℝ) < x := by exact_mod_cast hx
    have hlog : 0 < √(Real.log x) := Real.sqrt_pos.mpr (Real.log_pos hx1)
    exact div_ne_zero (mul_ne_zero hK (by positivity)) hlog.ne'
  exact (isEquivalent_iff_tendsto_one hv).mp
    (MetaMathlibExt.isEquivalent_card_primeFactors_three_mod_four hC)

/-- The integers all of whose prime factors are `≡ 3 (mod 4)` have natural density zero. -/
example {C : ℝ}
    (hC : Tendsto (fun x : ℕ => √(Real.log x) *
      ∏ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1), (1 - 1 / (q : ℝ)))
      atTop (nhds C)) :
    Tendsto (fun x : ℕ =>
      (((Finset.Icc 1 x).filter fun n => ∀ q ∈ n.primeFactors, q % 4 = 3).card : ℝ) / x)
      atTop (nhds 0) := by
  have h := (MetaMathlibExt.isEquivalent_card_primeFactors_three_mod_four hC).div
    (IsEquivalent.refl (u := fun x : ℕ => (x : ℝ)))
  refine h.symm.tendsto_nhds ?_
  have hsqrt : Tendsto (fun x : ℕ => √(Real.log x)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  refine ((tendsto_const_nhds (x := √(Real.exp Real.eulerMascheroniConstant / Real.pi) * C /
    2)).div_atTop hsqrt).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : (x : ℝ) ≠ 0 := by positivity
  simp only [Pi.div_apply]
  field_simp

end MetaMathlibExtTest.ThreeModFourIntegers
