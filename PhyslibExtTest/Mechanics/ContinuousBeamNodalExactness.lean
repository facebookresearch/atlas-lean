/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.ContinuousBeamStiffness
import MathlibExt.Interpolation.HermiteCubic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Two-span nodal-exactness checks

Concrete consumers of the two-span nodal-exactness results
in `PhyslibExt.Mechanics.ContinuousBeamStiffness`: a
symmetric uniform-load case (the symmetric realization of
the propped-cantilever reaction checks), an unequal-span
case with applied nodal moments and a negated-moment
control, and the interior field differing from the Hermite
cubic of its exact end data.

## i. Overview

These are non-vacuity, sign, and scope checks, not new
results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Symmetric two-span case
- B. Applied moments and sign control
- C. Interior field

## iv. References

- `PhyslibExt.Mechanics.ContinuousBeamStiffness`
- `MathlibExt.Interpolation.HermiteCubic`
-/

open Matrix
open Mechanics.EulerBernoulli

namespace PhyslibExtTest.Mechanics.ContinuousBeamNodalExactness

/-- Derivatives of an ascending-coefficient quartic. -/
private theorem quartic_iteratedDeriv {y : ℝ → ℝ} {a b c d e : ℝ}
    (hy : ∀ x : ℝ, y x = a + b * x + c * x ^ 2 + d * x ^ 3 + e * x ^ 4)
    (x : ℝ) :
    iteratedDeriv 1 y x = b + 2 * c * x + 3 * d * x ^ 2 + 4 * e * x ^ 3
    ∧ iteratedDeriv 2 y x = 2 * c + 6 * d * x + 12 * e * x ^ 2
    ∧ iteratedDeriv 3 y x = 6 * d + 24 * e * x
    ∧ iteratedDeriv 4 y x = 24 * e := by
  have hyfun : y = fun x => a + b * x ^ 1 + c * x ^ 2 + d * x ^ 3 + e * x ^ 4 := by
    funext x
    simp only [hy x, pow_one]
  rw [hyfun]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp (discharger := fun_prop) only [iteratedDeriv_fun_add,
        iteratedDeriv_const_mul_field, iteratedDeriv_pow, iteratedDeriv_const]
      norm_num [Nat.descFactorial]
      ring

/-! ## A. Symmetric two-span case -/

/-- Span 1 exact field for unit spans and load `48`. -/
private def y1A : ℝ → ℝ :=
  fun x => 0 + 1 * x + 0 * x ^ 2 + (-3) * x ^ 3 + 2 * x ^ 4

/-- Span 2 exact field for unit spans and load `48`. -/
private def y2A : ℝ → ℝ :=
  fun x => 0 + 0 * x + 3 * x ^ 2 + (-5) * x ^ 3 + 2 * x ^ 4

/-- Symmetric two-span check: every supported solution has
end data `(0, 1, 0, 0)` and `(0, 0, 0, -1)`, with outer
reaction `-3wL/8` and middle reaction `-5wL/4` at
`w = 48`, `L = 1`. -/
example : ∀ θ : Fin 3 → ℝ,
    supportedStiffness 1 1 1 1 *ᵥ θ
      = supportInjectionᵀ *ᵥ continuousBeamLoadVector 48 1 48 1 + 0 →
    spanOneGather *ᵥ (supportInjection *ᵥ θ) = ![0, 1, 0, 0]
      ∧ spanTwoGather *ᵥ (supportInjection *ᵥ θ) = ![0, 0, 0, -1]
      ∧ beamEndForces 1 1 y1A 0 = -(3 * 48 * 1 / 8)
      ∧ beamEndForces 1 1 y1A 2 + beamEndForces 1 1 y2A 0
          = -(5 * 48 * 1 / 4) := by
  intro θ hFE
  have hy1 : ∀ x : ℝ,
      y1A x = 0 + 1 * x + 0 * x ^ 2 + (-3) * x ^ 3 + 2 * x ^ 4 :=
    fun _ => rfl
  have hy2 : ∀ x : ℝ,
      y2A x = 0 + 0 * x + 3 * x ^ 2 + (-5) * x ^ 3 + 2 * x ^ 4 :=
    fun _ => rfl
  have D1 := quartic_iteratedDeriv hy1
  have D2 := quartic_iteratedDeriv hy2
  have hload1 : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (1 : ℝ) * iteratedDeriv 4 y1A x = 48 := by
    intro x _
    rw [(D1 x).2.2.2]
    norm_num
  have hload2 : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (1 : ℝ) * iteratedDeriv 4 y2A x = 48 := by
    intro x _
    rw [(D2 x).2.2.2]
    norm_num
  have hv : y1A 1 = y2A 0 := by norm_num [y1A, y2A]
  have hθ : iteratedDeriv 1 y1A 1 = iteratedDeriv 1 y2A 0 := by
    rw [(D1 1).1, (D2 0).1]
    norm_num
  have hs0 : y1A 0 = 0 := by norm_num [y1A]
  have hs1 : y1A 1 = 0 := by norm_num [y1A]
  have hs2 : y2A 1 = 0 := by norm_num [y2A]
  have hm0 : beamEndForces 1 1 y1A 1 = (0 : Fin 3 → ℝ) 0 := by
    norm_num [beamEndForces, (D1 0).2.1]
  have hm1 : beamEndForces 1 1 y1A 3 + beamEndForces 1 1 y2A 1
      = (0 : Fin 3 → ℝ) 1 := by
    norm_num [beamEndForces, (D1 1).2.1, (D2 0).2.1]
  have hm2 : beamEndForces 1 1 y2A 3 = (0 : Fin 3 → ℝ) 2 := by
    norm_num [beamEndForces, (D2 1).2.1]
  obtain ⟨h1, h2⟩ := continuousBeam_nodal_exact
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hy1 hy2 hload1 hload2 hv hθ hs0 hs1 hs2 0 hm0 hm1 hm2 hFE
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]
    ext i
    fin_cases i <;> norm_num [beamEndData, y1A, (D1 0).1, (D1 1).1]
  · rw [h2]
    ext i
    fin_cases i <;> norm_num [beamEndData, y2A, (D2 0).1, (D2 1).1]
  · norm_num [beamEndForces, (D1 0).2.2.1]
  · norm_num [beamEndForces, (D1 1).2.2.1, (D2 0).2.2.1]

/-! ## B. Applied moments and sign control -/

/-- Span 1 exact field for `EI = 3`, `L = 2`, `w = 5`. -/
private noncomputable def y1C : ℝ → ℝ :=
  fun x => 0 + 23 / 72 * x + (-1 / 6) * x ^ 2 + (-13 / 96) * x ^ 3
    + 5 / 72 * x ^ 4

/-- Span 2 exact field for `EI = 1`, `L = 3`, `w = 7`. -/
private noncomputable def y2C : ℝ → ℝ :=
  fun x => 0 + 1 / 4 * x + 49 / 16 * x ^ 2 + (-277 / 144) * x ^ 3
    + 7 / 24 * x ^ 4

/-- Direct supported-system check at the exact slopes. -/
private theorem caseC_exactSlopes_solve :
    supportedStiffness 3 2 1 3 *ᵥ ![23 / 72, 1 / 4, -29 / 16]
      = supportInjectionᵀ *ᵥ continuousBeamLoadVector 5 2 7 3
        + ![1, -2, 3] := by
  ext i
  fin_cases i <;>
    simp [supportedStiffness, continuousBeamStiffness,
      continuousBeamLoadVector, supportInjection, spanOneGather,
      spanTwoGather, beamStiffness, uniformLoadVector, Matrix.mulVec,
      dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_six, Fin.sum_univ_four, Fin.sum_univ_three] <;>
    norm_num

/-- Negated applied moments do not satisfy the same
supported system at the exact slopes. -/
example :
    supportedStiffness 3 2 1 3 *ᵥ ![23 / 72, 1 / 4, -29 / 16]
      ≠ supportInjectionᵀ *ᵥ continuousBeamLoadVector 5 2 7 3
        + ![-1, 2, -3] := by
  rw [caseC_exactSlopes_solve]
  intro h
  have h0 := congrFun h 0
  simp [Pi.add_apply] at h0
  linarith

/-- Applied-moment case: the exact-slope supported
solution has the two spans' exact end data. -/
example :
    spanOneGather *ᵥ (supportInjection *ᵥ ![23 / 72, 1 / 4, -29 / 16])
        = ![0, 23 / 72, 0, 1 / 4]
      ∧ spanTwoGather *ᵥ (supportInjection *ᵥ ![23 / 72, 1 / 4, -29 / 16])
        = ![0, 1 / 4, 0, -29 / 16] := by
  have hy1 : ∀ x : ℝ,
      y1C x = 0 + 23 / 72 * x + (-1 / 6) * x ^ 2 + (-13 / 96) * x ^ 3
        + 5 / 72 * x ^ 4 :=
    fun _ => rfl
  have hy2 : ∀ x : ℝ,
      y2C x = 0 + 1 / 4 * x + 49 / 16 * x ^ 2 + (-277 / 144) * x ^ 3
        + 7 / 24 * x ^ 4 :=
    fun _ => rfl
  have D1 := quartic_iteratedDeriv hy1
  have D2 := quartic_iteratedDeriv hy2
  have hload1 : ∀ x ∈ Set.Icc (0 : ℝ) 2,
      (3 : ℝ) * iteratedDeriv 4 y1C x = 5 := by
    intro x _
    rw [(D1 x).2.2.2]
    norm_num
  have hload2 : ∀ x ∈ Set.Icc (0 : ℝ) 3,
      (1 : ℝ) * iteratedDeriv 4 y2C x = 7 := by
    intro x _
    rw [(D2 x).2.2.2]
    norm_num
  have hv : y1C 2 = y2C 0 := by norm_num [y1C, y2C]
  have hθ : iteratedDeriv 1 y1C 2 = iteratedDeriv 1 y2C 0 := by
    rw [(D1 2).1, (D2 0).1]
    norm_num
  have hs0 : y1C 0 = 0 := by norm_num [y1C]
  have hs1 : y1C 2 = 0 := by norm_num [y1C]
  have hs2 : y2C 3 = 0 := by norm_num [y2C]
  have hm0 : beamEndForces 3 2 y1C 1
      = (![1, -2, 3] : Fin 3 → ℝ) 0 := by
    norm_num [beamEndForces, (D1 0).2.1]
  have hm1 : beamEndForces 3 2 y1C 3 + beamEndForces 1 3 y2C 1
      = (![1, -2, 3] : Fin 3 → ℝ) 1 := by
    norm_num [beamEndForces, (D1 2).2.1, (D2 0).2.1]
  have hm2 : beamEndForces 1 3 y2C 3
      = (![1, -2, 3] : Fin 3 → ℝ) 2 := by
    norm_num [beamEndForces, (D2 3).2.1]
  obtain ⟨h1, h2⟩ := continuousBeam_nodal_exact
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hy1 hy2 hload1 hload2 hv hθ hs0 hs1 hs2 ![1, -2, 3]
    hm0 hm1 hm2 caseC_exactSlopes_solve
  refine ⟨?_, ?_⟩
  · rw [h1]
    ext i
    fin_cases i <;> norm_num [beamEndData, y1C, (D1 0).1, (D1 2).1]
  · rw [h2]
    ext i
    fin_cases i <;> norm_num [beamEndData, y2C, (D2 0).1, (D2 3).1]

/-! ## C. Interior field -/

/-- At midspan the exact quartic is `1/4`, while the
Hermite cubic of its exact end data is `1/8`. -/
example :
    HermiteCubic.hermite 1 0 1 0 0 (1 / 2) = 1 / 8
      ∧ y1A (1 / 2) = 1 / 4 := by
  constructor <;> norm_num [HermiteCubic.hermite, y1A]

#print axioms
  Mechanics.EulerBernoulli.supportInjection_transpose_scatter
#print axioms
  Mechanics.EulerBernoulli.gather_continuousBeamNodalData
#print axioms
  Mechanics.EulerBernoulli.supportedStiffness_mulVec_nodalSlopes
#print axioms Mechanics.EulerBernoulli.continuousBeam_nodal_exact

end PhyslibExtTest.Mechanics.ContinuousBeamNodalExactness
