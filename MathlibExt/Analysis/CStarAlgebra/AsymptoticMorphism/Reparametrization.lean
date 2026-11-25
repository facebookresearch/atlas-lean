/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Basic

/-!
# Affine interpolation of half-line times

For T=[1,∞), a function r:T→T, t∈T and s∈[0,1], the interpolated time r_s(t)=s*t+(1-s)*r(t)
belongs to T. It equals r(t) at s=0 and t at s=1.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AsymptoticMorphism

/-- **Blended asymptotic time.**

Let T=AsymptoticTime=[1,∞), r:T→T, t∈T and s∈[0,1]. The time blendTime r t s is
s*t+(1-s)*r(t), which is at least 1.
-/
def blendTime (r : AsymptoticTime → AsymptoticTime)
    (t : AsymptoticTime) (s : unitInterval) : AsymptoticTime :=
  ⟨(s : ℝ) * (t : ℝ) + (1 - (s : ℝ)) * (r t : ℝ), by
    apply Set.mem_Ici.mpr
    have ht := mul_le_mul_of_nonneg_left t.property s.property.1
    have hr := mul_le_mul_of_nonneg_left (r t).property
      (sub_nonneg.mpr s.property.2)
    have hsum : (s : ℝ) + (1 - (s : ℝ)) = 1 := by
      rw [add_comm, sub_add_cancel]
    simpa only [mul_one, hsum] using add_le_add ht hr⟩

@[simp]
theorem blendTime_coe (r : AsymptoticTime → AsymptoticTime)
    (t : AsymptoticTime) (s : unitInterval) :
    (blendTime r t s : ℝ) =
      (s : ℝ) * (t : ℝ) + (1 - (s : ℝ)) * (r t : ℝ) := by
  rfl

@[simp]
theorem blendTime_zero (r : AsymptoticTime → AsymptoticTime) (t : AsymptoticTime) :
    blendTime r t 0 = r t := by
  apply Subtype.ext
  change (0 : ℝ) * (t : ℝ) + (1 - 0) * (r t : ℝ) = (r t : ℝ)
  simp

@[simp]
theorem blendTime_one (r : AsymptoticTime → AsymptoticTime) (t : AsymptoticTime) :
    blendTime r t 1 = t := by
  apply Subtype.ext
  change (1 : ℝ) * (t : ℝ) + (1 - 1) * (r t : ℝ) = (t : ℝ)
  simp

end AsymptoticMorphism
