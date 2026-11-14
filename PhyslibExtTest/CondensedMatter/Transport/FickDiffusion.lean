/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.Transport.FickDiffusion

/-! Tests for continuum diffusion (Fick's laws).

Overview
: Worked checks of the `CondensedMatter.Diffusion` module at concrete values:
  Gaussian PDE satisfaction, `erfc` boundary values, steady membrane flux, a
  non-constant-diffusivity countermodel, and scaling similarity.

Key results
: `gauss_pde_concrete`, `gauss_bothsides_concrete`, `erfc_surface_concrete`,
  `erfc_decay_concrete`, `steady_flux_concrete`, `countermodel_D_nonconstant`,
  `countermodel_continuity_fails`, `similarity_gauss_concrete`.

References
: Same frozen sources as `CondensedMatter.Diffusion` (see production module).
-/

open CondensedMatter.Diffusion

@[expose]
public section

namespace CondensedMatter.Diffusion.Test

/-- (a) Gaussian with `M = 1`, `D = 1` satisfies the PDE at `(x, t) = (0, 1)`. -/
theorem gauss_pde_concrete :
    deriv (fun t => gauss 1 1 0 t) 1
      = 1 * deriv (fun x => deriv (fun x' => gauss 1 1 x' 1) x) 0 :=
  gauss_pde 1 1 0 1 (by norm_num) (by norm_num)

/-- (a) Both PDE sides at `(0, 1)` equal `-(1 / √(4π)) / 2`. -/
theorem gauss_bothsides_concrete :
    deriv (fun t => gauss 1 1 0 t) 1 = -(1 / Real.sqrt (4 * Real.pi)) / 2
      ∧ 1 * deriv (fun x => deriv (fun x' => gauss 1 1 x' 1) x) 0
        = -(1 / Real.sqrt (4 * Real.pi)) / 2 := by
  have ht := (gauss_tderiv_value 1 1 0 1 (by norm_num) (by norm_num)).deriv
  have hxx := (gauss_xxderiv_value 1 1 0 1 (by norm_num) (by norm_num)).deriv
  have hg : gauss 1 1 0 1 = 1 / Real.sqrt (4 * Real.pi) := by
    simp only [gauss]
    have he : (-(0 : ℝ) ^ 2 / (4 * 1 * 1)) = 0 := by norm_num
    rw [he, Real.exp_zero, mul_one]
    congr 1
    congr 1
    ring
  constructor
  · rw [ht, hg]
    ring
  · rw [hxx, hg]
    ring

/-- (b) Maintained surface value at concrete numbers. -/
theorem erfc_surface_concrete : erfcProfile 2 1 0 1 = 2 :=
  erfcProfile_surface 2 1 1 (by norm_num) (by norm_num)

/-- (b) Interior value below the surface value at concrete numbers. -/
theorem erfc_decay_concrete : erfcProfile 2 1 1 1 < 2 := by
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have harg : (1 : ℝ) / Real.sqrt (4 * 1 * 1) = 1 / 2 := by
    have h4 : (4 : ℝ) * 1 * 1 = 4 := by ring
    rw [h4, hsqrt4]
  have hlt : erfc (1 / 2) < erfc 0 := by
    apply erfc_strictAnti
    all_goals (first | exact Set.mem_univ _ | norm_num)
  rw [erfc_zero] at hlt
  simp only [erfcProfile]
  rw [harg]
  calc (2 : ℝ) * erfc (1 / 2) < 2 * 1 := mul_lt_mul_of_pos_left hlt (by norm_num)
    _ = 2 := mul_one _

/-- (c) Steady membrane flux at concrete `c₁ = 3`, `c₂ = 1`, `L = 2`, `D = 5`. -/
theorem steady_flux_concrete : -5 * deriv (fun x' => steadyProfile 3 1 2 x') 0 = 5 := by
  have h := steady_flux 3 1 2 5 (by norm_num) 0
  rw [h]
  norm_num

/-- (d) The diffusivity `D̃(x) = x` is not constant, so the constant-`D`
hypothesis of C1 excludes it. -/
theorem countermodel_D_nonconstant : ¬ ∃ d : ℝ, ∀ x : ℝ, x = d := by
  rintro ⟨d, hd⟩
  have h0 := hd 0
  have h1 := hd 1
  linarith

/-- (d) With `c(x, t) = x^2` and flux `J = -x * (2 * x)` from the
non-constant `D̃(x) = x`, continuity `∂c/∂t + ∂J/∂x = 0` fails at `(1, 0)`. -/
theorem countermodel_continuity_fails :
    deriv (fun t : ℝ => (1 : ℝ) ^ 2) 0 + deriv (fun x : ℝ => -x * (2 * x)) 1 ≠ 0 := by
  have ht : deriv (fun t : ℝ => (1 : ℝ) ^ 2) 0 = 0 := by
    have hfun : (fun t : ℝ => (1 : ℝ) ^ 2) = (fun _ : ℝ => (1 : ℝ) ^ 2) := rfl
    rw [hfun]
    exact deriv_const _ _
  have hx : deriv (fun x : ℝ => -x * (2 * x)) 1 = -4 := by
    have h_eq : (fun x : ℝ => -x * (2 * x)) = (fun x : ℝ => -2 * x ^ 2) := by
      funext x
      ring
    rw [h_eq]
    have h_pow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * 1) 1 := by
      simpa using hasDerivAt_pow 2 (1 : ℝ)
    have h_mul : HasDerivAt (fun x : ℝ => -2 * x ^ 2) (-2 * (2 * 1)) 1 := by
      simpa [smul_eq_mul] using h_pow.const_mul (-2 : ℝ)
    have hval : (-2 * (2 * 1) : ℝ) = -4 := by norm_num
    have hd := h_mul.deriv
    rw [hval] at hd
    exact hd
  rw [ht, hx]
  norm_num

/-- (e) Gaussian self-similarity under doubling `(λ = 2)`. -/
theorem similarity_gauss_concrete (M D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    gauss M D (2 * x) (4 * t) = (1 / 2) * gauss M D x t := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hQ : (0 : ℝ) < 4 * Real.pi * D * t := by positivity
  have hsq : Real.sqrt (4 * Real.pi * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
  have hDt : (4 * D * t : ℝ) ≠ 0 := by positivity
  have h4D4t : (4 * D * (4 * t) : ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt (4 * Real.pi * D * (4 * t)) = 2 * Real.sqrt (4 * Real.pi * D * t) := by
    have hfactor : (4 * Real.pi * D * (4 * t) : ℝ) = 2 ^ 2 * (4 * Real.pi * D * t) := by ring
    rw [hfactor, Real.sqrt_mul (sq_nonneg 2), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hexp : (-(2 * x) ^ 2 / (4 * D * (4 * t)) : ℝ) = (-x ^ 2 / (4 * D * t)) := by
    field_simp
    ring
  simp only [gauss]
  rw [hsqrt, hexp]
  field_simp

#print axioms gauss_pde_concrete
#print axioms gauss_bothsides_concrete
#print axioms erfc_surface_concrete
#print axioms erfc_decay_concrete
#print axioms steady_flux_concrete
#print axioms countermodel_D_nonconstant
#print axioms countermodel_continuity_fails
#print axioms similarity_gauss_concrete

end CondensedMatter.Diffusion.Test

end
