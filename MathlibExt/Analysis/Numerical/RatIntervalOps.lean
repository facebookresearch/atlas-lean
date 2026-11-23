/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Numerical.Certified

@[expose] public section

namespace MathlibExt.Analysis.Numerical.Certified

namespace RatInterval

/- ## Interval multiplication and division (new).

The product (quotient) of two intervals encloses the product (quotient) of any
pair of enclosed points. Standard interval arithmetic; see Moore, R. E.,
*Interval Analysis*, Prentice-Hall, 1966, Ch. 2.
-/

/-- For `x ∈ [a₁, a₂]`, the product `x * y` lies between the endpoint products
`a₁ * y` and `a₂ * y`. -/
private theorem mul_mem_endpoints_left {x a₁ a₂ y : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) :
    min (a₁ * y) (a₂ * y) ≤ x * y ∧ x * y ≤ max (a₁ * y) (a₂ * y) := by
  rcases le_total 0 y with hy | hy
  · have h1 : a₁ * y ≤ x * y := mul_le_mul_of_nonneg_right ha.1 hy
    have h2 : x * y ≤ a₂ * y := mul_le_mul_of_nonneg_right ha.2 hy
    exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_right _ _)⟩
  · have h1 : a₂ * y ≤ x * y := mul_le_mul_of_nonpos_right ha.2 hy
    have h2 : x * y ≤ a₁ * y := mul_le_mul_of_nonpos_right ha.1 hy
    exact ⟨(min_le_right _ _).trans h1, h2.trans (le_max_left _ _)⟩

/-- For `y ∈ [b₁, b₂]`, the product `x * y` lies between the endpoint products
`x * b₁` and `x * b₂`. -/
private theorem mul_mem_endpoints_right {y b₁ b₂ x : ℝ}
    (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (x * b₁) (x * b₂) ≤ x * y ∧ x * y ≤ max (x * b₁) (x * b₂) := by
  rcases le_total 0 x with hx | hx
  · have h1 : x * b₁ ≤ x * y := mul_le_mul_of_nonneg_left hb.1 hx
    have h2 : x * y ≤ x * b₂ := mul_le_mul_of_nonneg_left hb.2 hx
    exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_right _ _)⟩
  · have h1 : x * b₂ ≤ x * y := mul_le_mul_of_nonpos_left hb.2 hx
    have h2 : x * y ≤ x * b₁ := mul_le_mul_of_nonpos_left hb.1 hx
    exact ⟨(min_le_right _ _).trans h1, h2.trans (le_max_left _ _)⟩

/-- Lower corner bound: `x * y` is at least the min of the four corner products. -/
private theorem mul_lower_bound {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂)) ≤ x * y := by
  have h1 := (mul_mem_endpoints_left (y := y) ha).1
  have h2a := (mul_mem_endpoints_right (x := a₁) hb).1
  have h2b := (mul_mem_endpoints_right (x := a₂) hb).1
  exact (min_le_min h2a h2b).trans h1

/-- Upper corner bound: `x * y` is at most the max of the four corner products. -/
private theorem mul_upper_bound {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    x * y ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := by
  have h1 := (mul_mem_endpoints_left (y := y) ha).2
  have h2a := (mul_mem_endpoints_right (x := a₁) hb).2
  have h2b := (mul_mem_endpoints_right (x := a₂) hb).2
  exact h1.trans (max_le_max h2a h2b)

/-- Interval multiplication: the endpoints are the min/max of the four endpoint
products (Moore, *Interval Analysis*, 1966, Ch. 2). -/
@[simps]
def mul (I J : RatInterval) : RatInterval :=
  ⟨min (min (I.lower * J.lower) (I.lower * J.upper))
      (min (I.upper * J.lower) (I.upper * J.upper)),
   max (max (I.lower * J.lower) (I.lower * J.upper))
      (max (I.upper * J.lower) (I.upper * J.upper))⟩

/-- Fundamental theorem of interval arithmetic for multiplication: the product
interval encloses the product of enclosed points. -/
theorem Encloses.mul {I J : RatInterval} {x y : ℝ}
    (hx : I.Encloses x) (hy : J.Encloses y) : (I.mul J).Encloses (x * y) := by
  rw [encloses_iff] at hx hy ⊢
  simp only [mul_lower, mul_upper, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  exact ⟨mul_lower_bound hx hy, mul_upper_bound hx hy⟩

/-- For nonnegative intervals, the product endpoints are the corner products
`lower * lower` and `upper * upper`. -/
theorem mul_of_nonneg {I J : RatInterval} (hIl : 0 ≤ I.lower) (hI : I.lower ≤ I.upper)
    (hJl : 0 ≤ J.lower) (hJ : J.lower ≤ J.upper) :
    I.mul J = ⟨I.lower * J.lower, I.upper * J.upper⟩ := by
  have hI0 : 0 ≤ I.upper := hIl.trans hI
  have hJ0 : 0 ≤ J.upper := hJl.trans hJ
  have hmin : min (min (I.lower * J.lower) (I.lower * J.upper))
      (min (I.upper * J.lower) (I.upper * J.upper)) = I.lower * J.lower := by
    apply le_antisymm
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact le_min (le_min le_rfl (mul_le_mul_of_nonneg_left hJ hIl))
        (le_min (mul_le_mul_of_nonneg_right hI hJl)
          ((mul_le_mul_of_nonneg_right hI hJl).trans
            (mul_le_mul_of_nonneg_left hJ hI0)))
  have hmax : max (max (I.lower * J.lower) (I.lower * J.upper))
      (max (I.upper * J.lower) (I.upper * J.upper)) = I.upper * J.upper := by
    apply le_antisymm
    · exact max_le (max_le
          ((mul_le_mul_of_nonneg_left hJ hIl).trans
            (mul_le_mul_of_nonneg_right hI hJ0))
          (mul_le_mul_of_nonneg_right hI hJ0))
        (max_le (mul_le_mul_of_nonneg_left hJ hI0) le_rfl)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  unfold mul
  rw [hmin, hmax]

/-- Interval reciprocal: the endpoints are the min/max of the endpoint
reciprocals. Total on `ℚ` (`0⁻¹ = 0`); meaningful only for intervals not
containing zero (Moore, *Interval Analysis*, 1966, Ch. 2). -/
@[simps]
def inv (J : RatInterval) : RatInterval :=
  ⟨min J.lower⁻¹ J.upper⁻¹, max J.lower⁻¹ J.upper⁻¹⟩

/-- Interval division, as multiplication by the reciprocal interval. -/
def div (I J : RatInterval) : RatInterval :=
  I.mul J.inv

/-- Fundamental theorem of interval arithmetic for reciprocals: for an interval
not containing zero, the reciprocal interval encloses the reciprocal of any
enclosed point. -/
theorem Encloses.inv {J : RatInterval} {y : ℝ}
    (h0 : J.upper < 0 ∨ 0 < J.lower) (hy : J.Encloses y) :
    J.inv.Encloses y⁻¹ := by
  rw [encloses_iff] at hy ⊢
  simp only [inv_lower, inv_upper, Rat.cast_min, Rat.cast_max, Rat.cast_inv]
  have hle : (J.lower : ℝ) ≤ (J.upper : ℝ) := hy.1.trans hy.2
  rcases h0 with hneg | hpos
  · have hU : (J.upper : ℝ) < 0 := by exact_mod_cast hneg
    have hL : (J.lower : ℝ) < 0 := lt_of_le_of_lt hle hU
    have hy0 : y < 0 := lt_of_le_of_lt hy.2 hU
    have e3 : (J.upper : ℝ)⁻¹ ≤ (J.lower : ℝ)⁻¹ :=
      (inv_le_inv_of_neg hU hL).mpr hle
    rw [min_eq_right e3, max_eq_left e3]
    exact ⟨(inv_le_inv_of_neg hU hy0).mpr hy.2, (inv_le_inv_of_neg hy0 hL).mpr hy.1⟩
  · have hL : (0 : ℝ) < J.lower := by exact_mod_cast hpos
    have hU : (0 : ℝ) < J.upper := lt_of_lt_of_le hL hle
    have hy0 : 0 < y := lt_of_lt_of_le hL hy.1
    have e3 : (J.upper : ℝ)⁻¹ ≤ (J.lower : ℝ)⁻¹ := (inv_le_inv₀ hU hL).mpr hle
    rw [min_eq_right e3, max_eq_left e3]
    exact ⟨(inv_le_inv₀ hU hy0).mpr hy.2, (inv_le_inv₀ hy0 hL).mpr hy.1⟩

/-- Fundamental theorem of interval arithmetic for division. -/
theorem Encloses.div {I J : RatInterval} {x y : ℝ}
    (h0 : J.upper < 0 ∨ 0 < J.lower) (hx : I.Encloses x) (hy : J.Encloses y) :
    (I.div J).Encloses (x / y) := by
  have h := Encloses.mul hx (Encloses.inv h0 hy)
  rw [div_eq_mul_inv]
  exact h

end RatInterval

end MathlibExt.Analysis.Numerical.Certified
