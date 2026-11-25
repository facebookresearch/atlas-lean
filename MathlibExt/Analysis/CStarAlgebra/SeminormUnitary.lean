/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Seminorm
public import Mathlib.Algebra.Star.Unitary

/-!
# Unit and unitary bounds for actual C-star seminorms

The square identity at the original unit forces its seminorm value to be zero
or one. The original unitary equation then bounds each unitary's value by one.
These facts provide the group-generator bounds used by maximal crossed-product
seminorms, including the zero seminorm.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarSeminorm

universe u

variable {B : Type u} [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

/-- **C*-seminorm of the unit.** For a unital complex star algebra `B` with scalar-compatible involution
and a C*-seminorm `p`, `p(1) ≤ 1`. This includes the zero seminorm. -/
theorem map_one_le (p : CStarSeminorm B) : p (1 : B) ≤ 1 := by
  have hsq : p (1 : B) ^ 2 = p (1 : B) := by
    simpa only [star_one, mul_one] using (p.map_star_mul_self (1 : B)).symm
  by_cases hzero : p (1 : B) = 0
  · rw [hzero]
    exact zero_le_one
  · have hone : p (1 : B) = 1 := by
      apply mul_left_cancel₀ hzero
      simpa only [mul_one, pow_two] using hsq
    exact hone.le

/-- **C*-seminorm of a unitary.** For a unital complex star algebra `B` with scalar-compatible
involution, a C*-seminorm `p`, and an algebraic unitary `u ∈ B`, one has `p(u) ≤ 1`. -/
theorem map_unitary_le (p : CStarSeminorm B) (u : unitary B) : p (u : B) ≤ 1 := by
  have hsq : p (u : B) ^ 2 = p (1 : B) := by
    rw [← p.map_star_mul_self (u : B), Unitary.star_mul_self_of_mem u.property]
  have hbound : p (u : B) ^ 2 ≤ 1 := hsq.trans_le p.map_one_le
  have hroot : p (u : B) ≤ Real.sqrt 1 :=
    (Real.le_sqrt (apply_nonneg p (u : B)) zero_le_one).mpr hbound
  simpa only [Real.sqrt_one] using hroot

end CStarSeminorm
