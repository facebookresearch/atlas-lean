/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.BeamStiffness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Beam-stiffness checks

Focused checks for `PhyslibExt.Mechanics.BeamStiffness`: a unit
tip deflection produces end force `12 * EI / L ^ 3` at the tip,
rigid translation produces no end forces, the factored energy
form is positive on a nonrigid tip deflection, the matrix is
positive semidefinite at unit data, and the rotation mode is
read back through the kernel-span characterization. The frame
checks use a nonrigid axial/bending vector, unit positive
semidefiniteness, and a three-mode rigid combination. The
uniform-load checks read back the load-vector entries, the
Hermite integrals, end data and end forces for `x ^ 2`, and the
rigid linear quartic identity.

These are elaboration and non-vacuity checks, not new results.
-/

open Matrix Mechanics.EulerBernoulli intervalIntegral

/-- Unit tip deflection: tip force entry is `12` at `EI = L = 1`. -/
example : (beamStiffness 1 1 *ᵥ ![0, 0, 1, 0]) 2 = 12 := by
  norm_num [beamStiffness, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- Rigid translation has zero energy. -/
example : (![1, 0, 1, 0] : Fin 4 → ℝ) ⬝ᵥ (beamStiffness 1 1 *ᵥ ![1, 0, 1, 0]) = 0 := by
  rw [beamStiffness_mulVec_translation]
  simp

/-- Nonrigid unit tip deflection has energy value `12` from the
factored quadratic form. -/
example : (![0, 0, 1, 0] : Fin 4 → ℝ)
    ⬝ᵥ (beamStiffness 1 1 *ᵥ ![0, 0, 1, 0]) = 12 := by
  rw [beamStiffness_quad_form_factor]
  norm_num

/-- The unit-data stiffness matrix is positive semidefinite. -/
example : (beamStiffness 1 1).PosSemidef :=
  beamStiffness_posSemidef (by norm_num) (by norm_num)

/-- The rotation mode is read back as a rigid-span element. -/
example : ∃ a b : ℝ,
    (![0, 1, 2, 1] : Fin 4 → ℝ)
      = a • ![1, 0, 1, 0] + b • ![0, 1, 2, 1] :=
  (beamStiffness_mulVec_eq_zero_iff (by norm_num) (by norm_num)
    ![0, 1, 2, 1]).1 (beamStiffness_mulVec_rotation 5 2)

/-- Nonrigid frame data has the factored energy value `419 / 2`
at `EA = 11`, `EI = 5`, `L = 2`. -/
example : (![1, 2, -1, 4, 0, 3] : Fin 6 → ℝ)
    ⬝ᵥ (frameStiffness 11 5 2 *ᵥ ![1, 2, -1, 4, 0, 3])
    = 419 / 2 := by
  rw [frameStiffness_quad_form_factor]
  norm_num

/-- Pure axial stretch has positive frame energy `11 / 2`. -/
example : (![0, 0, 0, 1, 0, 0] : Fin 6 → ℝ)
    ⬝ᵥ (frameStiffness 11 5 2 *ᵥ ![0, 0, 0, 1, 0, 0])
    = 11 / 2 := by
  rw [frameStiffness_quad_form_factor]
  norm_num

/-- The unit-data frame matrix is positive semidefinite. -/
example : (frameStiffness 1 1 1).PosSemidef :=
  frameStiffness_posSemidef (by norm_num) (by norm_num) (by norm_num)

/-- A combination of the three planar rigid modes is in the
frame kernel. -/
example : frameStiffness 11 5 2 *ᵥ
    ((3 : ℝ) • ![1, 0, 0, 1, 0, 0]
      + (2 : ℝ) • ![0, 1, 0, 0, 1, 0]
      + (-1 : ℝ) • ![0, 0, 1, 0, 2, 1]) = 0 :=
  (frameStiffness_mulVec_eq_zero_iff (by norm_num) (by norm_num)
    (by norm_num) _).2 ⟨3, 2, -1, rfl⟩

/-- Uniform load vector entries at `w = 2`, `L = 3`. -/
example : uniformLoadVector 2 3 = ![3, 3 / 2, 3, -3 / 2] := by
  funext i
  fin_cases i <;> norm_num [uniformLoadVector]

/-- The Hermite consistent-load integrals are the entries of
the uniform load vector at `w = 2`, `L = 3`. -/
example : (∫ x in (0 : ℝ)..3,
      (2 : ℝ) * HermiteCubic.hermite 3 1 0 0 0 x
      = uniformLoadVector 2 3 0)
    ∧ (∫ x in (0 : ℝ)..3,
      (2 : ℝ) * HermiteCubic.hermite 3 0 1 0 0 x
      = uniformLoadVector 2 3 1)
    ∧ (∫ x in (0 : ℝ)..3,
      (2 : ℝ) * HermiteCubic.hermite 3 0 0 1 0 x
      = uniformLoadVector 2 3 2)
    ∧ (∫ x in (0 : ℝ)..3,
      (2 : ℝ) * HermiteCubic.hermite 3 0 0 0 1 x
      = uniformLoadVector 2 3 3) :=
  uniformLoadVector_entries_hermite (by norm_num)

/-- End data and conjugate end forces for `y = x ^ 2` at
`EI = 3`, `L = 2`. -/
example : beamEndData 2 (fun x : ℝ => x ^ 2) = ![0, 0, 4, 4]
    ∧ beamEndForces 3 2 (fun x : ℝ => x ^ 2) = ![0, -6, 0, 6] := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [beamEndData, beamEndForces] <;> norm_num

/-- The rigid linear field `y = x` is a zero-load quartic with
zero conjugate end forces, through the quartic identity. -/
example : beamEndForces 5 2 (fun x : ℝ => x) = 0 := by
  have hload : ∀ x ∈ Set.Icc (0 : ℝ) 2,
      (5 : ℝ) * iteratedDeriv 4 (fun x : ℝ => x) x = 0 := by
    intro x _hx
    rw [show (fun x : ℝ => x) = (· ^ 1) by funext y; simp]
    simp only [iteratedDeriv_pow,
      show Nat.descFactorial 1 4 = 0 from by decide]
    norm_num
  have h := quartic_end_force_identity (EI := 5) (L := 2) (w := 0)
    (y := fun x : ℝ => x) (a := 0) (b := 1) (c := 0) (d := 0)
    (e := 0) (by norm_num) (by norm_num)
    (by intro x; ring) hload
  rw [h]
  have hdata : beamEndData 2 (fun x : ℝ => x) = ![0, 1, 2, 1] := by
    funext i
    fin_cases i <;> simp [beamEndData]
  rw [hdata]
  simp [uniformLoadVector, beamStiffness_mulVec_rotation]
