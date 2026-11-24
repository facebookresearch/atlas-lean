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
# The actual affine interpolation of reparametrized time

This constructs only the half-line time point. No homotopy or asymptotic
defect law is assumed as data.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AsymptoticMorphism

/-- The printed r_s(t)=s*t+(1-s)*r(t), staying in the genuine time half-line. -/
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
