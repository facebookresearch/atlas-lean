/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LegendreTransform

/-! Client properties and the unbounded-zero-conjugate regression. -/

@[expose] public section

open scoped InnerProductSpace
open MathlibExt.Probability.LegendreTransform

namespace MathlibExtTest.Probability.LegendreTransform

/-- The original real quadratic Fenchel–Young property follows from its finite conjugate. -/
example {d : ℕ} (l x : EuclideanSpace ℝ (Fin d)) :
    ⟪l, x⟫_ℝ - ‖l‖ ^ 2 / 2 ≤ ‖x‖ ^ 2 / 2 := by
  have hFY := le_legendreTransform
    (Λ := fun y : EuclideanSpace ℝ (Fin d) => ((‖y‖ ^ 2 / 2 : ℝ) : EReal))
    (x := x) (l := l)
  rw [legendreTransform_norm_sq_div_two, ← EReal.coe_sub] at hFY
  exact EReal.coe_le_coe_iff.mp hFY

/-- The original antitonicity property, with extended-real function values. -/
example {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    legendreTransform (fun y : EuclideanSpace ℝ (Fin d) => ((‖y‖ ^ 2 : ℝ) : EReal)) x
      ≤ legendreTransform (fun y : EuclideanSpace ℝ (Fin d) => ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) x := by
  apply legendreTransform_antitone
  intro y
  exact EReal.coe_le_coe_iff.mpr (by linarith [sq_nonneg ‖y‖])

/-- The original real quadratic convexity property uses proved finiteness. -/
example {d : ℕ} :
    ConvexOn ℝ Set.univ (fun x =>
      (legendreTransform (fun y : EuclideanSpace ℝ (Fin d) =>
        ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) x).toReal) := by
  apply convexOn_legendreTransform
  intro x
  rw [legendreTransform_norm_sq_div_two]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

/-- The original quadratic double-transform bound in the extended-real API. -/
example {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    legendreTransform
        (legendreTransform (fun y : EuclideanSpace ℝ (Fin d) => ((‖y‖ ^ 2 / 2 : ℝ) : EReal))) x
      ≤ ((‖x‖ ^ 2 / 2 : ℝ) : EReal) := by
  apply legendreTransform_legendreTransform_le
  intro y
  exact EReal.coe_ne_bot _

/-- The zero function has a finite zero conjugate at the origin. -/
example : legendreTransform (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : EReal)) 0 = 0 :=
  legendreTransform_zero

/-- At the original nonzero test point, the correct conjugate is `⊤`. -/
example : legendreTransform (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : EReal))
    (EuclideanSpace.single (0 : Fin 2) 1) = ⊤ := by
  apply legendreTransform_zero_of_ne
  intro h
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v (0 : Fin 2)) h
  norm_num at h0

/-- The original concrete quadratic value remains `9/2`, explicitly embedded into `EReal`. -/
example : legendreTransform (fun y : EuclideanSpace ℝ (Fin 1) => ((‖y‖ ^ 2 / 2 : ℝ) : EReal))
    (EuclideanSpace.single (0 : Fin 1) 3) = ((9 / 2 : ℝ) : EReal) := by
  rw [legendreTransform_norm_sq_div_two]
  congr 1
  norm_num [EuclideanSpace.norm_eq]

#print axioms legendreTransform_norm_sq_div_two
#print axioms convexOn_legendreTransform
#print axioms legendreTransform_legendreTransform_le
#print axioms legendreTransform_zero
#print axioms legendreTransform_zero_of_ne

end MathlibExtTest.Probability.LegendreTransform
