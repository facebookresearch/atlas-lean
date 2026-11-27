/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Dynamics.PlanarStability
import Domains.Biology.Ecology.NicholsonBailey
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.PDE.SemilinearFlow.Instability

open Function MathlibExt.Biology.Ecology.NicholsonBailey

private theorem growth_one (a c : ℝ) (ha : 0 < a) :
    ∀ x ∈ positiveQuadrant, ¬ IsFixedPt (step 1 a c) x :=
  fun _ hx => not_isFixedPt_of_le_one zero_lt_one le_rfl ha hx

private theorem growth_half (a c : ℝ) (ha : 0 < a) :
    ∀ x ∈ positiveQuadrant, ¬ IsFixedPt (step (1 / 2) a c) x :=
  fun _ hx => not_isFixedPt_of_le_one (by norm_num) (by norm_num) ha hx

private theorem trivial_equilibrium (r a c : ℝ) :
    IsFixedPt (step r a c) 0 ∧ (0 : ℝ × ℝ) ∉ positiveQuadrant ∧
      jacobian r a c 0 = !![r, 0; 0, 0] := by
  exact ⟨isFixedPt_zero r a c, by simp [positiveQuadrant], by simp [jacobian]⟩

private theorem concrete_equilibrium :
    positiveEquilibrium 2 1 1 = (2 * Real.log 2, Real.log 2) := by
  norm_num [positiveEquilibrium]

private theorem concrete_fixed_point :
    positiveEquilibrium 2 1 1 ∈ positiveQuadrant ∧
      IsFixedPt (step 2 1 1) (positiveEquilibrium 2 1 1) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : Real.exp (-Real.log 2) = (2 : ℝ)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
  rw [concrete_equilibrium]
  refine ⟨⟨mul_pos (by norm_num) hlog, hlog⟩, ?_⟩
  apply Prod.ext <;> simp [step, he] <;> ring

private theorem concrete_jacobian :
    jacobian 2 1 1 (positiveEquilibrium 2 1 1) =
      !![1, -(2 * Real.log 2); 1 / 2, Real.log 2] := by
  have he : Real.exp (-Real.log 2) = (2 : ℝ)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
  rw [concrete_equilibrium]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [jacobian, he] <;> ring

private theorem concrete_spectral_data :
    let J := jacobian 2 1 1 (positiveEquilibrium 2 1 1)
    J.trace = 1 + Real.log 2 ∧ J.det = 2 * Real.log 2 ∧
      1 < J.det ∧ J.trace ^ 2 < 4 * J.det := by
  dsimp
  rw [concrete_jacobian, Matrix.trace_fin_two, Matrix.det_fin_two]
  have hu : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ))
      (by norm_num) (by norm_num)
    linarith
  have hl : (1 : ℝ) / 2 < Real.log 2 := by
    have h := Real.log_lt_sub_one_of_pos (x := ((2 : ℝ)⁻¹))
      (by norm_num) (by norm_num)
    rw [Real.log_inv] at h
    linarith
  have hdisc : (1 + Real.log 2) ^ 2 < 4 * (2 * Real.log 2) := by
    have h := mul_pos (sub_pos.mpr hu) (show 0 < 3 + Real.log 2 by linarith)
    nlinarith
  simp
  constructor
  · ring
  · constructor <;> linarith

private def scale (a c : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (a * c * x.1, a * x.2)

private theorem scale_step (r a c : ℝ) (x : ℝ × ℝ) :
    scale a c (step r a c x) = step r 1 1 (scale a c x) := by
  apply Prod.ext <;> simp [scale, step] <;> ring

private theorem scale_bijective {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Function.Bijective (scale a c) := by
  have hac : a * c ≠ 0 := mul_ne_zero ha.ne' hc.ne'
  constructor
  · intro x y h
    exact Prod.ext (mul_left_cancel₀ hac (congrArg Prod.fst h))
      (mul_left_cancel₀ ha.ne' (congrArg Prod.snd h))
  · intro y
    refine ⟨(y.1 / (a * c), y.2 / a), ?_⟩
    apply Prod.ext <;> dsimp [scale] <;> field_simp [ha.ne', hc.ne']

private theorem scale_quadrant {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (x : ℝ × ℝ) :
    scale a c x ∈ positiveQuadrant ↔ x ∈ positiveQuadrant := by
  change (0 < a * c * x.1 ∧ 0 < a * x.2) ↔ (0 < x.1 ∧ 0 < x.2)
  constructor
  · rintro ⟨hH, hP⟩
    exact ⟨pos_of_mul_pos_right hH (mul_pos ha hc).le,
      pos_of_mul_pos_right hP ha.le⟩
  · rintro ⟨hH, hP⟩
    exact ⟨mul_pos (mul_pos ha hc) hH, mul_pos ha hP⟩

private theorem scale_equilibrium {r a c : ℝ}
    (hr : 1 < r) (ha : 0 < a) (hc : 0 < c) :
    scale a c (positiveEquilibrium r a c) = positiveEquilibrium r 1 1 := by
  have hr1 : r - 1 ≠ 0 := sub_ne_zero.mpr hr.ne'
  apply Prod.ext <;> simp [scale, positiveEquilibrium]
  · field_simp [ha.ne', hc.ne', hr1]
  · field_simp [ha.ne']

/-- The headline spectral theorem on the concrete instance `r = 2`, `a = 1`, `c = 1`: the
Jacobian at the positive equilibrium has two nonreal conjugate eigenvalues of modulus
`√(2 log 2) > 1`. -/
private theorem concrete_spectrum :
    ∃ z : ℂ, 0 < z.im ∧
      spectrum ℂ ((jacobian 2 1 1 (positiveEquilibrium 2 1 1)).map (algebraMap ℝ ℂ)) =
        {z, star z} ∧
      ‖z‖ = Real.sqrt (2 * Real.log 2) ∧ ‖star z‖ = ‖z‖ ∧ 1 < ‖z‖ := by
  obtain ⟨z, him, hspec, hnorm, hstar, hz⟩ :=
    spectrum_jacobian_positiveEquilibrium (r := 2) (a := 1) (c := 1)
      (by norm_num) one_pos one_pos
  refine ⟨z, him, hspec, ?_, hstar, hz⟩
  rw [hnorm]
  norm_num

/-- The eigenvalue modulus of the concrete instance agrees with its Jacobian determinant:
`‖z‖ ^ 2 = det J = 2 log 2`. -/
private theorem concrete_spectrum_norm_sq :
    ∃ z : ℂ, z ∈ spectrum ℂ
        ((jacobian 2 1 1 (positiveEquilibrium 2 1 1)).map (algebraMap ℝ ℂ)) ∧
      ‖z‖ ^ 2 = (jacobian 2 1 1 (positiveEquilibrium 2 1 1)).det := by
  obtain ⟨z, -, hspec, hnorm, -, -⟩ := concrete_spectrum
  refine ⟨z, by rw [hspec]; simp, ?_⟩
  obtain ⟨-, hdet, -, -⟩ := concrete_spectral_data
  rw [hnorm, Real.sq_sqrt (by positivity), hdet]

/-- The headline instability theorem on the concrete instance `r = 2`, `a = 1`, `c = 1`, with
the equilibrium `(2 log 2, log 2)` written out: positive initial states arbitrarily near it have
forward iterates a fixed positive distance away. -/
private theorem concrete_lyapunovUnstable :
    ∃ ε > 0, ∀ δ > 0, ∃ x₀ ∈ positiveQuadrant,
      ‖x₀ - (2 * Real.log 2, Real.log 2)‖ < δ ∧
      ∃ n : ℕ, ε ≤ ‖(step 2 1 1)^[n] x₀ - (2 * Real.log 2, Real.log 2)‖ := by
  have h := positiveEquilibrium_lyapunovUnstable (r := 2) (a := 1) (c := 1)
    (by norm_num) one_pos one_pos
  rwa [concrete_equilibrium] at h

#print axioms mapsTo_step_positiveQuadrant
#print axioms mapsTo_iterate_step_positiveQuadrant
#print axioms not_isFixedPt_of_le_one
#print axioms isFixedPt_zero
#print axioms growth_one
#print axioms growth_half
#print axioms trivial_equilibrium
#print axioms concrete_equilibrium
#print axioms concrete_fixed_point
#print axioms concrete_jacobian
#print axioms concrete_spectral_data
#print axioms scale_step
#print axioms scale_bijective
#print axioms scale_quadrant
#print axioms scale_equilibrium
#print axioms spectrum_jacobian_positiveEquilibrium
#print axioms positiveEquilibrium_lyapunovUnstable
#print axioms concrete_spectrum
#print axioms concrete_spectrum_norm_sq
#print axioms concrete_lyapunovUnstable

open MathlibExt.Biology.Dynamics.PlanarStability
open MathlibExt.Analysis.PDE.SemilinearFlow.Instability

#check mem_spectrum_iff_isCharRoot
#check exists_escape_of_spectralRadius_eq

#print axioms mem_spectrum_iff_isCharRoot
#print axioms exists_escape_of_spectralRadius_eq
