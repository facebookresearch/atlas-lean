/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.TwoGood
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
/-!
# Cobb–Douglas demand

For the normalized two-good Cobb–Douglas utility `u(x) = x₀ ^ α * x₁ ^ (1 - α)` with
`0 < α < 1`, positive prices and nonnegative wealth, the budget-share bundle
`(α w / p₀, (1 - α) w / p₁)` maximizes utility over the budget set: global optimality, proved with
weighted AM–GM (`Real.geom_mean_le_arith_mean2_weighted`), with no first-order conditions. The
expenditure shares of the demand are the exponents.

## Main definitions

* `cobbDouglas α`: the utility `x₀ ^ α * x₁ ^ (1 - α)` (real powers).
* `cobbDouglasDemand α p w`: the budget-share bundle.

## Main results

* `isMarshallianDemand_cobbDouglas`: the budget-share bundle is a Marshallian demand on the
  nonnegative orthant.
* `cobbDouglasDemand_shares`: `p₀ x₀ = α w` and `p₁ x₁ = (1 - α) w`.

Atlas roadmap target EC03.T01.

## References

* H. R. Varian, *Intermediate Microeconomics*, 9th ed., Norton (2014), ch. 5.
* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University
  Press (1995), ch. 3.
-/

@[expose] public section

namespace MathlibExt.Economics.Consumer

open Matrix

/-- The normalized two-good Cobb–Douglas utility `u(x) = x₀ ^ α * x₁ ^ (1 - α)`
(real powers; the exponents `α` and `1 - α` sum to one). -/
noncomputable def cobbDouglas (α : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  x 0 ^ α * x 1 ^ (1 - α)

/-- The Cobb–Douglas budget-share bundle: spend the share `α` of wealth on good `0`
and `1 - α` on good `1`, i.e. `x₀ = α w / p₀` and `x₁ = (1 - α) w / p₁`. -/
noncomputable def cobbDouglasDemand (α : ℝ) (p : Fin 2 → ℝ) (w : ℝ) : Fin 2 → ℝ :=
  ![α * w / p 0, (1 - α) * w / p 1]

/-- **Cobb–Douglas demand.** With exponent `0 < α < 1`, positive prices and
nonnegative wealth, the budget-share bundle maximizes `cobbDouglas α` over the budget set
in the nonnegative orthant. -/
theorem isMarshallianDemand_cobbDouglas {α w : ℝ} {p : Fin 2 → ℝ} (hα₀ : 0 < α)
    (hα₁ : α < 1) (hp : ∀ i, 0 < p i) (hw : 0 ≤ w) :
    IsMarshallianDemand (cobbDouglas α) twoGoodSet p w (cobbDouglasDemand α p w) := by
  have h1α : 0 < 1 - α := by linarith
  have hαne : α ≠ 0 := ne_of_gt hα₀
  have h1αne : (1 - α) ≠ 0 := ne_of_gt h1α
  have hp0 : 0 < p 0 := hp 0
  have hp1 : 0 < p 1 := hp 1
  have hp0ne : p 0 ≠ 0 := ne_of_gt hp0
  have hp1ne : p 1 ≠ 0 := ne_of_gt hp1
  have hd0 : cobbDouglasDemand α p w 0 = α * w / p 0 := by simp [cobbDouglasDemand]
  have hd1 : cobbDouglasDemand α p w 1 = (1 - α) * w / p 1 := by
    simp [cobbDouglasDemand]
  have hd0nn : 0 ≤ cobbDouglasDemand α p w 0 := by
    rw [hd0]
    exact div_nonneg (mul_nonneg (le_of_lt hα₀) hw) (le_of_lt hp0)
  have hd1nn : 0 ≤ cobbDouglasDemand α p w 1 := by
    rw [hd1]
    exact div_nonneg (mul_nonneg (le_of_lt h1α) hw) (le_of_lt hp1)
  have hsh0 : p 0 * cobbDouglasDemand α p w 0 = α * w := by
    rw [hd0]
    field_simp
  have hsh1 : p 1 * cobbDouglasDemand α p w 1 = (1 - α) * w := by
    rw [hd1]
    field_simp
  have hdot : ∀ x : Fin 2 → ℝ, p ⬝ᵥ x = p 0 * x 0 + p 1 * x 1 := by
    intro x
    simp only [dotProduct, Fin.sum_univ_two]
  have hmem : cobbDouglasDemand α p w ∈ budgetSet twoGoodSet p w := by
    change cobbDouglasDemand α p w ∈ twoGoodSet ∧
      p ⬝ᵥ cobbDouglasDemand α p w ≤ w
    constructor
    · intro i
      fin_cases i
      · exact hd0nn
      · exact hd1nn
    · have hdot2 : p ⬝ᵥ cobbDouglasDemand α p w = w := by
        rw [hdot, hsh0, hsh1]
        ring
      exact le_of_eq hdot2
  refine ⟨hmem, fun y hy => ?_⟩
  have hy' : y ∈ twoGoodSet ∧ p ⬝ᵥ y ≤ w := hy
  obtain ⟨hyX, hyB⟩ := hy'
  have hyX' : ∀ i, 0 ≤ y i := hyX
  have hy0 : 0 ≤ y 0 := hyX' 0
  have hy1 : 0 ≤ y 1 := hyX' 1
  rw [hdot] at hyB
  by_cases hw0 : w = 0
  · subst hw0
    have ha : 0 ≤ p 0 * y 0 := mul_nonneg (le_of_lt hp0) hy0
    have hb : 0 ≤ p 1 * y 1 := mul_nonneg (le_of_lt hp1) hy1
    have ha0 : p 0 * y 0 = 0 := by linarith
    have hb0 : p 1 * y 1 = 0 := by linarith
    have hy0z : y 0 = 0 := by
      rcases mul_eq_zero.mp ha0 with h | h
      · exact absurd h hp0ne
      · exact h
    have hy1z : y 1 = 0 := by
      rcases mul_eq_zero.mp hb0 with h | h
      · exact absurd h hp1ne
      · exact h
    have hu0 : cobbDouglas α y = 0 := by
      simp only [cobbDouglas, hy0z, hy1z, Real.zero_rpow hαne, Real.zero_rpow h1αne,
        mul_zero]
    have hudnn : 0 ≤ cobbDouglas α (cobbDouglasDemand α p 0) := by
      simp only [cobbDouglas]
      exact mul_nonneg (Real.rpow_nonneg hd0nn _) (Real.rpow_nonneg hd1nn _)
    rw [hu0]
    exact hudnn
  · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    have hwne : w ≠ 0 := hw0
    have hs0 : 0 < α * w := mul_pos hα₀ hwpos
    have hs1 : 0 < (1 - α) * w := mul_pos h1α hwpos
    have hαwne : α * w ≠ 0 := mul_ne_zero hαne hwne
    have h1αwne : (1 - α) * w ≠ 0 := mul_ne_zero h1αne hwne
    have hz0 : 0 ≤ p 0 * y 0 / (α * w) :=
      div_nonneg (mul_nonneg (le_of_lt hp0) hy0) (le_of_lt hs0)
    have hz1 : 0 ≤ p 1 * y 1 / ((1 - α) * w) :=
      div_nonneg (mul_nonneg (le_of_lt hp1) hy1) (le_of_lt hs1)
    have hAMGM : (p 0 * y 0 / (α * w)) ^ α * (p 1 * y 1 / ((1 - α) * w)) ^ (1 - α)
        ≤ α * (p 0 * y 0 / (α * w)) + (1 - α) * (p 1 * y 1 / ((1 - α) * w)) := by
      apply Real.geom_mean_le_arith_mean2_weighted
      all_goals first
        | exact le_of_lt hα₀
        | exact le_of_lt h1α
        | exact hz0
        | exact hz1
        | ring
    have he0 : α * (p 0 * y 0 / (α * w)) = p 0 * y 0 / w := by
      field_simp
    have he1 : (1 - α) * (p 1 * y 1 / ((1 - α) * w)) = p 1 * y 1 / w := by
      field_simp
    have hsum : α * (p 0 * y 0 / (α * w)) + (1 - α) * (p 1 * y 1 / ((1 - α) * w))
        = (p 0 * y 0 + p 1 * y 1) / w := by
      rw [he0, he1, add_div]
    have hle1 : (p 0 * y 0 + p 1 * y 1) / w ≤ 1 := by
      rw [div_le_iff₀ hwpos, one_mul]
      exact hyB
    have hZle : (p 0 * y 0 / (α * w)) ^ α * (p 1 * y 1 / ((1 - α) * w)) ^ (1 - α)
        ≤ 1 := by
      calc (p 0 * y 0 / (α * w)) ^ α * (p 1 * y 1 / ((1 - α) * w)) ^ (1 - α)
          ≤ α * (p 0 * y 0 / (α * w)) + (1 - α) * (p 1 * y 1 / ((1 - α) * w)) :=
            hAMGM
        _ = (p 0 * y 0 + p 1 * y 1) / w := hsum
        _ ≤ 1 := hle1
    have hA0 : 0 ≤ α * w / p 0 :=
      div_nonneg (mul_nonneg (le_of_lt hα₀) (le_of_lt hwpos)) (le_of_lt hp0)
    have hA1 : 0 ≤ (1 - α) * w / p 1 :=
      div_nonneg (mul_nonneg (le_of_lt h1α) (le_of_lt hwpos)) (le_of_lt hp1)
    have hsc0 : (α * w / p 0) * (p 0 * y 0 / (α * w)) = y 0 := by
      field_simp
    have hsc1 : ((1 - α) * w / p 1) * (p 1 * y 1 / ((1 - α) * w)) = y 1 := by
      field_simp
    have hrw0 : y 0 ^ α = (α * w / p 0) ^ α * (p 0 * y 0 / (α * w)) ^ α := by
      conv_lhs => rw [← hsc0]
      exact Real.mul_rpow hA0 hz0
    have hrw1 : y 1 ^ (1 - α)
        = ((1 - α) * w / p 1) ^ (1 - α) * (p 1 * y 1 / ((1 - α) * w)) ^ (1 - α) := by
      conv_lhs => rw [← hsc1]
      exact Real.mul_rpow hA1 hz1
    have hud : cobbDouglas α (cobbDouglasDemand α p w)
        = (α * w / p 0) ^ α * ((1 - α) * w / p 1) ^ (1 - α) := by
      simp only [cobbDouglas, hd0, hd1]
    have hfactor : cobbDouglas α y = cobbDouglas α (cobbDouglasDemand α p w)
        * ((p 0 * y 0 / (α * w)) ^ α * (p 1 * y 1 / ((1 - α) * w)) ^ (1 - α)) := by
      have huy : cobbDouglas α y = y 0 ^ α * y 1 ^ (1 - α) := rfl
      rw [huy, hrw0, hrw1, hud]
      ring
    have hudnn : 0 ≤ cobbDouglas α (cobbDouglasDemand α p w) := by
      rw [hud]
      exact mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hA1 _)
    rw [hfactor]
    calc cobbDouglas α (cobbDouglasDemand α p w)
          * ((p 0 * y 0 / (α * w)) ^ α * (p 1 * y 1 / ((1 - α) * w)) ^ (1 - α))
        ≤ cobbDouglas α (cobbDouglasDemand α p w) * 1 :=
          mul_le_mul_of_nonneg_left hZle hudnn
      _ = cobbDouglas α (cobbDouglasDemand α p w) := mul_one _

/-- The expenditure shares of the Cobb–Douglas demand are the exponents:
`p₀ x₀ = α w` and `p₁ x₁ = (1 - α) w`. -/
theorem cobbDouglasDemand_shares {α w : ℝ} {p : Fin 2 → ℝ} (hp : ∀ i, 0 < p i) :
    p 0 * cobbDouglasDemand α p w 0 = α * w ∧
      p 1 * cobbDouglasDemand α p w 1 = (1 - α) * w := by
  have h0 : p 0 ≠ 0 := ne_of_gt (hp 0)
  have h1 : p 1 ≠ 0 := ne_of_gt (hp 1)
  have e0 : cobbDouglasDemand α p w 0 = α * w / p 0 := by simp [cobbDouglasDemand]
  have e1 : cobbDouglasDemand α p w 1 = (1 - α) * w / p 1 := by simp [cobbDouglasDemand]
  rw [e0, e1]
  constructor <;> field_simp

end MathlibExt.Economics.Consumer
