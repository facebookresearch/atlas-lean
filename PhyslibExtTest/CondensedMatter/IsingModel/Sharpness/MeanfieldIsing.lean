/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.MeanfieldIsing
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.MeanfieldIsing`

Non-vacuity of `meanfield_lower_bound` at `β₀ = 1`: the square-root profile
`m(β) = √(1 - (1/β)²)` satisfies every repaired hypothesis. Its square is
`1 - β⁻²` on `[1, ∞)`, hence continuous on `Ici 1`, differentiable on `Ioi 1`
with derivative `2/β³ = (2/β)(1 - m(β)²)`, and `m(1) = 0`, `m ≥ 0`. Applying
`meanfield_lower_bound` recovers its bound, which this profile attains with
equality, for instance `m(2) = √3 / 2`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.MeanfieldIsing

open Real Set Filter Topology
open _root_.StatMech.Sharpness

/-- The square-root profile `√(1 - (1/β)²)`, the equality case of the
mean-field lower bound at `β₀ = 1`. -/
noncomputable def sqrtProfile : ℝ → ℝ := fun β => Real.sqrt (1 - (1 / β) ^ 2)

lemma sqrtProfile_sq {β : ℝ} (hβ : 1 ≤ β) : (sqrtProfile β) ^ 2 = 1 - (β ^ 2)⁻¹ := by
  have harg : 0 ≤ 1 - (1 / β) ^ 2 := by
    have h : (1 / β) ^ 2 ≤ 1 := by
      rw [div_pow, one_pow, div_le_one (by positivity : (0 : ℝ) < β ^ 2)]
      nlinarith
    linarith
  have h : (sqrtProfile β) ^ 2 = 1 - (1 / β) ^ 2 := Real.sq_sqrt harg
  rw [h, div_pow, one_pow, one_div]

lemma sqrtProfile_sq_continuousOn :
    ContinuousOn (fun β => (sqrtProfile β) ^ 2) (Ici 1) := by
  have hmodel : ContinuousOn (fun β : ℝ => 1 - (β ^ 2)⁻¹) (Ici 1) := by
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.inv₀
    · exact (continuous_pow 2).continuousOn
    · intro β hβ
      exact pow_ne_zero 2 (by linarith [mem_Ici.mp hβ] : β ≠ 0)
  apply hmodel.congr
  intro β hβ
  exact sqrtProfile_sq (mem_Ici.mp hβ)

lemma sqrtProfile_sq_eventuallyEq {β : ℝ} (hβ : 1 < β) :
    (fun β => (sqrtProfile β) ^ 2) =ᶠ[𝓝 β] (fun β => 1 - (β ^ 2)⁻¹) := by
  filter_upwards [Ioi_mem_nhds hβ] with x hx
  exact sqrtProfile_sq (le_of_lt (mem_Ioi.mp hx))

lemma sqrtProfile_sq_differentiableAt :
    ∀ β ∈ Ioi (1 : ℝ), DifferentiableAt ℝ (fun β => (sqrtProfile β) ^ 2) β := by
  intro β hβ
  have hβ1 : 1 < β := mem_Ioi.mp hβ
  have hmodel : DifferentiableAt ℝ (fun β => 1 - (β ^ 2)⁻¹) β :=
    (differentiableAt_const 1).sub
      ((differentiableAt_pow 2).inv (pow_ne_zero 2 (by linarith : β ≠ 0)))
  exact hmodel.congr_of_eventuallyEq (sqrtProfile_sq_eventuallyEq hβ1)

lemma sqrtProfile_sq_deriv {β : ℝ} (hβ : 1 < β) :
    deriv (fun β => (sqrtProfile β) ^ 2) β = 2 / β ^ 3 := by
  have hβ0 : β ≠ 0 := by linarith
  have hmodel : HasDerivAt (fun β => 1 - (β ^ 2)⁻¹) (2 / β ^ 3) β := by
    have hpow : HasDerivAt (fun β : ℝ => β ^ 2) (2 * β) β := by
      simpa using (hasDerivAt_pow 2 β)
    have hsub := (hasDerivAt_const β (1 : ℝ)).sub (hpow.inv (pow_ne_zero 2 hβ0))
    convert hsub using 1
    field_simp
    ring
  rw [(sqrtProfile_sq_eventuallyEq hβ).deriv_eq]
  exact hmodel.deriv

lemma sqrtProfile_sq_differential_le :
    ∀ β ∈ Ioi (1 : ℝ),
      (2 / β) * (1 - (sqrtProfile β) ^ 2) ≤ deriv (fun β => (sqrtProfile β) ^ 2) β := by
  intro β hβ
  have hβ1 : 1 < β := mem_Ioi.mp hβ
  rw [sqrtProfile_sq_deriv hβ1, sqrtProfile_sq hβ1.le]
  have hβ0 : β ≠ 0 := by linarith
  apply le_of_eq
  field_simp
  ring

lemma sqrtProfile_one : sqrtProfile 1 = 0 := by
  show Real.sqrt (1 - (1 / (1 : ℝ)) ^ 2) = 0
  norm_num

lemma sqrtProfile_nonneg : ∀ β ∈ Ici (1 : ℝ), 0 ≤ sqrtProfile β :=
  fun β _ => Real.sqrt_nonneg (1 - (1 / β) ^ 2)

/-- The square-root profile attains the mean-field lower bound at `β = 2`. -/
lemma sqrtProfile_two : sqrtProfile 2 = Real.sqrt 3 / 2 := by
  show Real.sqrt (1 - (1 / (2 : ℝ)) ^ 2) = Real.sqrt 3 / 2
  rw [show (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 by norm_num,
    Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

-- `meanfield_lower_bound` applied to the square-root profile at `β₀ = 1`.
example {β : ℝ} (hβ : 1 ≤ β) : Real.sqrt (1 - (1 / β) ^ 2) ≤ sqrtProfile β :=
  meanfield_lower_bound 1 one_pos sqrtProfile sqrtProfile_sq_continuousOn
    sqrtProfile_sq_differentiableAt sqrtProfile_sq_differential_le sqrtProfile_one
    sqrtProfile_nonneg hβ

-- At `β = 2` the bound reads `√3 / 2 ≤ m(2)`, and it is attained.
example : Real.sqrt 3 / 2 ≤ sqrtProfile 2 ∧ sqrtProfile 2 = Real.sqrt 3 / 2 := by
  have h := meanfield_lower_bound 1 one_pos sqrtProfile sqrtProfile_sq_continuousOn
    sqrtProfile_sq_differentiableAt sqrtProfile_sq_differential_le sqrtProfile_one
    sqrtProfile_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  have h2 : Real.sqrt (1 - ((1 : ℝ) / 2) ^ 2) = Real.sqrt 3 / 2 := sqrtProfile_two
  rw [h2] at h
  exact ⟨h, sqrtProfile_two⟩

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.MeanfieldIsing
