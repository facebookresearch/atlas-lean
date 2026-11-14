/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Quantum.OneDimensionalModels

/-!
# One-dimensional model system checks

Concrete consumers of `Chemistry.Quantum.OneDimensionalModels`: box
eigen-equation and Dirichlet checks, box orthonormality diagonal and
off-diagonal instances, oscillator `v = 0` checks, ladder-commutator
instances, box moment checks, and a polyene rational-arithmetic probe.
-/

namespace Chemistry.Quantum.OneDimensionalModelsTest

open Chemistry.Quantum.OneDimensionalModels

/-- Box eigen-equation numeric check (`n = 1`, `L = m = ħ = 1`, `x = 1/4`). -/
example : -(1 ^ 2 / (2 * 1)) * deriv (deriv (boxFunction 1 1)) (1 / 4)
    = boxEnergy 1 1 1 1 * boxFunction 1 1 (1 / 4) :=
  box_eigen_equation 1 1 1 1 (1 / 4) (by norm_num) (by norm_num) (by norm_num)

/-- Box energy value pin: `E_1 = π^2 / 2` for `L = m = ħ = 1`. -/
example : boxEnergy 1 1 1 1 = Real.pi ^ 2 / 2 := by
  unfold boxEnergy
  push_cast
  ring

/-- Box function value pin: `ψ_1(1/2) = √2` for `L = 1`. -/
example : boxFunction 1 1 (1 / 2) = Real.sqrt 2 := by
  have e : (1:ℝ) * Real.pi * (1/2) / (1:ℝ) = Real.pi / 2 := by ring
  have h2 : (2/(1:ℝ)) = 2 := by norm_num
  simp only [boxFunction, Nat.cast_one, e, h2, Real.sin_pi_div_two, mul_one]

/-- Dirichlet boundary at `0` (`n = 1`, `L = 1`). -/
example : boxFunction 1 1 0 = 0 :=
  box_dirichlet_zero 1 1 (by norm_num) (by norm_num)

/-- Dirichlet boundary at `L` (`n = 1`, `L = 1`). -/
example : boxFunction 1 1 1 = 0 :=
  box_dirichlet_right 1 1 (by norm_num) (by norm_num)

/-- Box orthonormality diagonal (`n = k = 1`, `L = 1`). -/
example : ∫ x in (0:ℝ)..1, boxFunction 1 1 x * boxFunction 1 1 x = 1 := by
  have h := box_orthonormality 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  simpa using h

/-- Box orthonormality off-diagonal (`n = 1`, `k = 2`, `L = 1`). -/
example : ∫ x in (0:ℝ)..1, boxFunction 1 1 x * boxFunction 2 1 x = 0 := by
  have h := box_orthonormality 1 2 1 (by norm_num) (by norm_num) (by norm_num)
  simpa using h

/-- Oscillator `v = 0` eigen-equation at `x = 0` (`ħ = m = ω = 1` units). -/
example : -(1 / 2) * deriv (deriv oscFun0) 0
      + (1 / 2) * ((((0:ℝ) ^ 2 : ℝ)) : ℂ) * oscFun0 0
    = (1 / 2) * oscFun0 0 :=
  osc_eigen_0 0

/-- Oscillator `(0, 0)` orthonormality. -/
example : ∫ x : ℝ, oscFun0 x * oscFun0 x = 1 :=
  osc_orthonormality_00

/-- Oscillator `(0, 1)` orthonormality (odd-vanishing pair). -/
example : ∫ x : ℝ, oscFun0 x * oscFun1 x = 0 :=
  osc_orthonormality_01

/-- Oscillator `(1, 0)` orthonormality (odd-vanishing pair). -/
example : ∫ x : ℝ, oscFun1 x * oscFun0 x = 0 :=
  osc_orthonormality_10

/-- Oscillator `(1, 1)` orthonormality (diagonal). -/
example : ∫ x : ℝ, oscFun1 x * oscFun1 x = 1 :=
  osc_orthonormality_11

/-- Oscillator `(0, 2)` orthonormality (even off-diagonal). -/
example : ∫ x : ℝ, oscFun0 x * oscFun2 x = 0 :=
  osc_orthonormality_02

/-- Oscillator `(2, 0)` orthonormality (even off-diagonal). -/
example : ∫ x : ℝ, oscFun2 x * oscFun0 x = 0 :=
  osc_orthonormality_20

/-- Oscillator `(1, 2)` orthonormality (odd-vanishing pair). -/
example : ∫ x : ℝ, oscFun1 x * oscFun2 x = 0 :=
  osc_orthonormality_12

/-- Oscillator `(2, 1)` orthonormality (odd-vanishing pair). -/
example : ∫ x : ℝ, oscFun2 x * oscFun1 x = 0 :=
  osc_orthonormality_21

/-- Oscillator `(2, 2)` orthonormality (diagonal). -/
example : ∫ x : ℝ, oscFun2 x * oscFun2 x = 1 :=
  osc_orthonormality_22

/-- Ladder commutator on the zero Schwartz function. -/
example (x : ℝ) : annFun (creFun 0) x - creFun (annFun 0) x
    = (0 : ℝ → ℂ) x :=
  ladder_commutator_schwartz 0 ⟨0, rfl⟩ x

/-- Ladder commutator `(of_hasDerivAt)` on the concrete function `x ↦ ↑x`. -/
example (x : ℝ) : annFun (creFun (fun x : ℝ => (x : ℂ))) x
      - creFun (annFun (fun x : ℝ => (x : ℂ))) x = (x : ℂ) := by
  have h1 : ∀ y : ℝ, HasDerivAt (fun x : ℝ => (x : ℂ)) 1 y := by
    intro y
    simpa only [id_eq, Complex.ofReal_one] using (hasDerivAt_id y).ofReal_comp
  have hder : deriv (fun x : ℝ => (x : ℂ)) = fun _ => 1 := by
    funext y
    exact (h1 y).deriv
  have hf' : HasDerivAt (deriv (fun x : ℝ => (x : ℂ))) 0 x := by
    rw [hder]
    exact hasDerivAt_const x 1
  exact ladder_commutator_of_hasDerivAt _ _ _ x (h1 x) hf'

/-- Box position mean `⟨x⟩ = 1/2` (`n = 1`, `L = 1`). -/
example : ∫ x in (0:ℝ)..1, x * (boxFunction 1 1 x) ^ 2 = 1 / 2 :=
  box_moment_x 1 1 (by norm_num) (by norm_num)

/-- Box position second moment (`n = 1`, `L = 1`). -/
example : ∫ x in (0:ℝ)..1, x ^ 2 * (boxFunction 1 1 x) ^ 2
    = 1 ^ 2 * (1 / 3 - 1 / (2 * 1 ^ 2 * Real.pi ^ 2)) := by
  have h := box_moment_x2 1 1 (by norm_num) (by norm_num)
  simpa using h

/-- PROBE (rational-arithmetic check of the MODEL closed form, not a
physical prediction): `k = 2` gives `20 / π` in probe units
(`a = m = ħ = c = 1`, so `L = 5`, `h = 2π`). -/
example : polyeneWavelength 2 (polyeneLength 2 1) 1 1 1 = 20 / Real.pi := by
  have h := polyene_wavelength_closed_form 2 1 1 1 1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  unfold polyeneLength planckH
  push_cast
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hD1 : ((2 * Real.pi * 1) * (2 * 2 + 1) : ℝ) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (by norm_num))
      (by norm_num)
  field_simp
  try ring

end Chemistry.Quantum.OneDimensionalModelsTest
