/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Cauchy stress, small strain, and Mohr's circle

3D Cauchy stress (tension-positive) with traction, principal stresses, invariants, and the
hydrostatic/deviatoric split; 2D stress transformation with Mohr's circle and in-plane maximum
shear; small strain with a rigid-motion check; and true strain and true stress.

## i. Overview

Stress is tension-positive throughout, and reference geometry (area `A₀`) is distinguished from
current geometry (area `A`). Symmetry of the Cauchy stress is a model assumption: angular-momentum
balance without body couples (no couple stresses) is the model input that licenses treating `σ`
as symmetric. It is carried as the explicit hypothesis `IsSymmetricStress` wherever it is used,
and this module does not claim to derive symmetry from force balance alone.

The traction on a face with normal `n` is `t = σ *ᵥ n`. It flips sign on opposite faces and is
linear in `n`, both as direct `mulVec` consequences; the statements hold for general `n`, and the
unit-normal case `‖n‖ = 1` is the physical reading. Given symmetry, Mathlib's spectral theorem
for Hermitian matrices (`Matrix.IsHermitian.spectral_theorem`, reused, not re-proved) gives real
principal stresses, an orthonormal eigenbasis, and the spectral decomposition; for real symmetric
matrices conjugation by the eigenvector unitary is conjugation by an orthogonal matrix. The
invariants `I₁ = trace σ`, `I₂ = (trace² - trace σ²)/2`, `I₃ = det σ` are invariant under
orthogonal conjugation by trace/determinant cyclicity. The split `σ = p • 1 + s` with
`p = trace σ / 3` is unique and orthogonal for the Frobenius inner product
`⟨A, B⟩ = trace (Aᵀ * B)`.

In 2D, `R θ` rotates the coordinate axes by `θ` (the physical rotation by `-θ`), which is the
convention for which the standard transformation formulas for `σ₂' = R θ * σ₂ * (R θ)ᵀ` hold.
They imply Mohr's circle equation and, in the 1-3 principal plane, the maximum-shear bound
`τmax = (s₁ - s₃)/2` attained at `θ = π/4`. The in-plane scope is explicit: the claim that the
global 3D maximum shear is attained in that plane is a documented consequence (the 3D extremum
argument), not separately proved here.

Small strain `ε = (H + Hᵀ)/2` is the symmetrized displacement gradient, a stated small-strain
approximation; it is symmetric, vanishes for infinitesimal rigid motions, and finite rotations are
not in this module's scope. Engineering shear is `γ_xy = 2 ε_xy`. True strain `ln(1+e)` comes
with upper and lower bounds on `e > -1`, and true stress `σ = s(1+e)` follows from the volume-
constancy model hypothesis for uniaxial incompressible deformation.

No constitutive law (no Hooke's law or elasticity tensor), no finite-strain measures, no
yield/failure criteria, and no beam or pressure-vessel applications.

## ii. Key results

- `Elasticity.traction_neg` : traction flips sign on the opposite face.
- `Elasticity.traction_linear` : traction is linear in the normal vector.
- `Elasticity.principalStresses_real` : principal stresses are real.
- `Elasticity.spectral_decomposition` : the spectral decomposition of `σ`.
- `Elasticity.principalDirection_eigen` : the eigenvector equation for principal directions.
- `Elasticity.stressInvariant1_conjugate`, `Elasticity.stressInvariant2_conjugate`,
  `Elasticity.stressInvariant3_conjugate` : invariance of `I₁`, `I₂`, `I₃` under orthogonal
  conjugation.
- `Elasticity.stress_split`, `Elasticity.trace_deviatoric`, `Elasticity.stress_split_unique`,
  `Elasticity.stress_split_orthogonal` : the unique orthogonal hydrostatic/deviatoric split.
- `Elasticity.rotatedStress2_00`, `Elasticity.rotatedStress2_11`,
  `Elasticity.rotatedStress2_01` : the 2D stress transformation formulas.
- `Elasticity.mohr_circle` : Mohr's circle equation.
- `Elasticity.principalPlaneShear_bound`, `Elasticity.principalPlaneShear_max` : the in-plane
  maximum shear bound and its attainment at `θ = π/4`.
- `Elasticity.smallStrain_symmetric` : small strain is symmetric.
- `Elasticity.displacementGradient_affine` : the gradient of an affine field is its matrix.
- `Elasticity.smallStrain_rigid` : infinitesimal rigid motions have zero small strain.
- `Elasticity.simpleShear_strain`, `Elasticity.simpleShear_engineering` : tensor and engineering
  shear of simple shear.
- `Elasticity.trueStrain_le`, `Elasticity.trueStrain_lt`, `Elasticity.trueStrain_lower` : upper
  and lower bounds for true strain.
- `Elasticity.trueStress_of_volumeConstancy` : `σ_true = s(1+e)` from volume constancy.

## iii. Table of contents

- A. Symmetric stress and traction
- B. Principal stresses, invariants, and the deviatoric split
- C. Plane-stress transformation, Mohr's circle, and maximum shear
- D. Small strain, true strain, and true stress

## iv. References

* DoITPoMS (Cambridge) TLP Library, "Stress Analysis and Mohr's Circle" and "Analysis of
  Deformation Processes", for Cauchy stress, traction, principal stresses, Mohr's circle, and
  small/true strain.
* MIT OCW 3.032 Mechanical Behavior of Materials, and MITx 3.032.1x, for stress transformations
  and linear elastic behavior.

-/

@[expose] public section

open scoped Matrix

namespace Elasticity

/-! ## A. Symmetric stress and traction -/
/-- Cauchy stress symmetry as a model assumption (no body couples). -/
def IsSymmetricStress {n : ℕ} (σ : Matrix (Fin n) (Fin n) ℝ) : Prop := σᵀ = σ

/-- Traction vector on a face with normal `v`: `t = σ v`. -/
def traction {n : ℕ} (σ : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : Fin n → ℝ :=
  σ *ᵥ v

/-- Action-reaction: traction flips sign on the opposite face. -/
lemma traction_neg {n : ℕ} (σ : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    traction σ (-v) = -traction σ v := by
  simp only [traction, ← Matrix.mulVecLin_apply, map_neg]

/-- Traction is linear in the normal vector (direct `mulVec` consequence). -/
lemma traction_linear {n : ℕ} (σ : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ)
    (v w : Fin n → ℝ) :
    traction σ (a • v + b • w) = a • traction σ v + b • traction σ w := by
  simp only [traction, ← Matrix.mulVecLin_apply, map_add, map_smul]

/-! ## B. Principal stresses, invariants, and the deviatoric split -/

/-- A real symmetric stress matrix is Hermitian (for real entries `star` is trivial). -/
lemma symmetric_isHermitian (σ : Matrix (Fin 3) (Fin 3) ℝ)
    (h : IsSymmetricStress σ) : σ.IsHermitian := by
  have hT : σᵀ = σ := h
  unfold Matrix.IsHermitian
  ext i j
  rw [Matrix.conjTranspose_apply, star_trivial]
  have h2 := congrFun (congrFun hT j) i
  rw [Matrix.transpose_apply] at h2
  exact h2.symm

/-- Principal stresses are real: the Mathlib eigenvalues of a symmetric matrix lie in its
real spectrum. Uses `Matrix.IsHermitian.eigenvalues_mem_spectrum_real`. -/
lemma principalStresses_real (σ : Matrix (Fin 3) (Fin 3) ℝ)
    (h : IsSymmetricStress σ) (i : Fin 3) :
    (symmetric_isHermitian σ h).eigenvalues i ∈ spectrum ℝ σ :=
  Matrix.IsHermitian.eigenvalues_mem_spectrum_real (symmetric_isHermitian σ h) i

/-- Spectral decomposition of a symmetric stress matrix, in Mathlib's
`Matrix.IsHermitian.spectral_theorem` shape: conjugation of the diagonal eigenvalue matrix by
the eigenvector unitary. For real symmetric matrices this is conjugation by an orthogonal
matrix (`star` is trivial, so `ᴴ = ᵀ`). -/
lemma spectral_decomposition (σ : Matrix (Fin 3) (Fin 3) ℝ)
    (h : IsSymmetricStress σ) :
    σ = ((Unitary.conjStarAlgAut ℝ (Matrix (Fin 3) (Fin 3) ℝ))
      (symmetric_isHermitian σ h).eigenvectorUnitary)
      (Matrix.diagonal (RCLike.ofReal ∘ (symmetric_isHermitian σ h).eigenvalues)) :=
  Matrix.IsHermitian.spectral_theorem (symmetric_isHermitian σ h)

/-- The eigenvectors from Mathlib's spectral theorem diagonalize `σ`. -/
lemma principalDirection_eigen (σ : Matrix (Fin 3) (Fin 3) ℝ)
    (h : IsSymmetricStress σ) (j : Fin 3) :
    σ.mulVec ((symmetric_isHermitian σ h).eigenvectorBasis j).ofLp
      = (symmetric_isHermitian σ h).eigenvalues j •
        ((symmetric_isHermitian σ h).eigenvectorBasis j).ofLp :=
  Matrix.IsHermitian.mulVec_eigenvectorBasis (symmetric_isHermitian σ h) j

/-- First stress invariant `I₁ = trace σ`. -/
def stressInvariant1 (σ : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := σ.trace

/-- Second stress invariant `I₂ = (trace² - trace σ²)/2`. -/
noncomputable def stressInvariant2 (σ : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (σ.trace ^ 2 - (σ * σ).trace) / 2

/-- Third stress invariant `I₃ = det σ`. -/
def stressInvariant3 (σ : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := σ.det

/-- Helper: the trace is invariant under orthogonal conjugation. -/
lemma trace_conjugate (M Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Qᵀ * Q = 1) :
    (Q * M * Qᵀ).trace = M.trace := by
  calc (Q * M * Qᵀ).trace
      = (Qᵀ * (Q * M)).trace := Matrix.trace_mul_comm _ _
    _ = ((Qᵀ * Q) * M).trace := by rw [← mul_assoc]
    _ = M.trace := by rw [hQ, one_mul]

/-- `I₁` is invariant under orthogonal conjugation. -/
lemma stressInvariant1_conjugate (σ Q : Matrix (Fin 3) (Fin 3) ℝ)
    (h1Q : Qᵀ * Q = 1) (_h2Q : Q * Qᵀ = 1) :
    stressInvariant1 (Q * σ * Qᵀ) = stressInvariant1 σ :=
  trace_conjugate σ Q h1Q

/-- `I₂` is invariant under orthogonal conjugation. -/
lemma stressInvariant2_conjugate (σ Q : Matrix (Fin 3) (Fin 3) ℝ)
    (h1Q : Qᵀ * Q = 1) (_h2Q : Q * Qᵀ = 1) :
    stressInvariant2 (Q * σ * Qᵀ) = stressInvariant2 σ := by
  have hQQ : (Q * σ * Qᵀ) * (Q * σ * Qᵀ) = Q * (σ * σ) * Qᵀ := by
    have e : ∀ X : Matrix (Fin 3) (Fin 3) ℝ, Qᵀ * (Q * X) = X := fun X => by
      rw [← mul_assoc, h1Q, one_mul]
    simp only [mul_assoc]
    rw [e]
  unfold stressInvariant2
  rw [trace_conjugate σ Q h1Q, hQQ, trace_conjugate (σ * σ) Q h1Q]

/-- `I₃` is invariant under orthogonal conjugation. -/
lemma stressInvariant3_conjugate (σ Q : Matrix (Fin 3) (Fin 3) ℝ)
    (h1Q : Qᵀ * Q = 1) (_h2Q : Q * Qᵀ = 1) :
    stressInvariant3 (Q * σ * Qᵀ) = stressInvariant3 σ := by
  have hd : Q.det * Q.det = 1 := by
    have h := congrArg Matrix.det h1Q
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    exact h
  unfold stressInvariant3
  calc (Q * σ * Qᵀ).det
      = Q.det * (σ.det * Qᵀ.det) := by rw [Matrix.det_mul, Matrix.det_mul, mul_assoc]
    _ = σ.det * (Q.det * Q.det) := by rw [Matrix.det_transpose]; ring
    _ = σ.det := by rw [hd, mul_one]

/-- Hydrostatic pressure (mean normal stress) `p = trace σ / 3`. -/
noncomputable def hydrostaticPressure (σ : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := σ.trace / 3

/-- Deviatoric stress `s = σ - p • 1`. -/
noncomputable def deviatoricStress (σ : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  σ - hydrostaticPressure σ • 1

/-- Helper: the 3x3 identity has trace 3. -/
lemma trace_one_fin3 : (1 : Matrix (Fin 3) (Fin 3) ℝ).trace = 3 := by
  simp [Matrix.trace_one, Fintype.card_fin]

/-- The hydrostatic/deviatoric split reconstructs `σ`. -/
lemma stress_split (σ : Matrix (Fin 3) (Fin 3) ℝ) :
    σ = hydrostaticPressure σ • 1 + deviatoricStress σ := by
  unfold deviatoricStress
  rw [add_comm]
  exact (sub_add_cancel σ _).symm

/-- The deviatoric stress is traceless. -/
lemma trace_deviatoric (σ : Matrix (Fin 3) (Fin 3) ℝ) :
    (deviatoricStress σ).trace = 0 := by
  unfold deviatoricStress hydrostaticPressure
  rw [Matrix.trace_sub, Matrix.trace_smul, trace_one_fin3, smul_eq_mul]
  ring

/-- The hydrostatic/deviatoric split is unique. -/
lemma stress_split_unique (σ : Matrix (Fin 3) (Fin 3) ℝ) (p₁ : ℝ)
    (s₁ : Matrix (Fin 3) (Fin 3) ℝ)
    (hdecomp : σ = p₁ • 1 + s₁) (htr : s₁.trace = 0) :
    p₁ = hydrostaticPressure σ ∧ s₁ = deviatoricStress σ := by
  have htrσ : σ.trace = p₁ * 3 := by
    have h := congrArg Matrix.trace hdecomp
    rw [Matrix.trace_add, Matrix.trace_smul, trace_one_fin3, htr] at h
    simpa [smul_eq_mul] using h
  have hp : p₁ = hydrostaticPressure σ := by
    unfold hydrostaticPressure
    rw [htrσ]
    ring
  refine ⟨hp, ?_⟩
  unfold deviatoricStress
  rw [← hp, hdecomp, add_sub_cancel_left]

/-- The split is orthogonal for the Frobenius inner product `⟨A, B⟩ = trace (Aᵀ * B)`. -/
lemma stress_split_orthogonal (σ : Matrix (Fin 3) (Fin 3) ℝ) :
    ((hydrostaticPressure σ • 1)ᵀ * deviatoricStress σ).trace = 0 := by
  have hT : (hydrostaticPressure σ • (1 : Matrix (Fin 3) (Fin 3) ℝ))ᵀ
      = hydrostaticPressure σ • 1 := by
    rw [Matrix.transpose_smul, Matrix.transpose_one]
  have hmul : (hydrostaticPressure σ • 1) * deviatoricStress σ
      = hydrostaticPressure σ • deviatoricStress σ := by
    rw [smul_mul_assoc, one_mul]
  rw [hT, hmul, Matrix.trace_smul, trace_deviatoric, smul_zero]

/-! ## C. Plane-stress transformation, Mohr's circle, and maximum shear -/

/-- 2D rotation matrix for the stress transformation. Convention: `R θ` rotates the coordinate
axes by `θ` (equivalently the physical rotation by `-θ`); this is the convention for which the
standard transformation formulas below hold with `σ₂' = R θ * σ₂ * (R θ)ᵀ`. -/
noncomputable def rotationMatrix2 (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

/-- The 2D rotation matrix is orthogonal: `Rᵀ * R = 1`. -/
lemma rotationMatrix2_transpose_mul (θ : ℝ) :
    (rotationMatrix2 θ)ᵀ * rotationMatrix2 θ = 1 := by
  unfold rotationMatrix2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
    first | linear_combination Real.cos_sq_add_sin_sq θ | ring

/-- The 2D rotation matrix is orthogonal: `R * Rᵀ = 1`. -/
lemma rotationMatrix2_mul_transpose (θ : ℝ) :
    rotationMatrix2 θ * (rotationMatrix2 θ)ᵀ = 1 := by
  unfold rotationMatrix2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
    first | linear_combination Real.cos_sq_add_sin_sq θ | ring

/-- 2D stress after rotating the axes by `θ`: `σ₂' = R θ * σ₂ * (R θ)ᵀ`. -/
noncomputable def rotatedStress2 (σ₂ : Matrix (Fin 2) (Fin 2) ℝ) (θ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  rotationMatrix2 θ * σ₂ * (rotationMatrix2 θ)ᵀ

/-- Transformation formula for the normal stress `σx'`. -/
lemma rotatedStress2_00 (σx σy τ θ : ℝ) :
    rotatedStress2 !![σx, τ; τ, σy] θ 0 0
      = (σx + σy) / 2 + (σx - σy) / 2 * Real.cos (2 * θ)
        + τ * Real.sin (2 * θ) := by
  have hexpand : rotatedStress2 !![σx, τ; τ, σy] θ 0 0
      = σx * Real.cos θ ^ 2 + 2 * τ * Real.cos θ * Real.sin θ
        + σy * Real.sin θ ^ 2 := by
    simp [rotatedStress2, rotationMatrix2, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply]
    ring
  rw [hexpand, Real.cos_two_mul', Real.sin_two_mul]
  have hcs := Real.cos_sq_add_sin_sq θ
  linear_combination ((σx + σy) / 2) * hcs

/-- Transformation formula for the normal stress `σy'`. -/
lemma rotatedStress2_11 (σx σy τ θ : ℝ) :
    rotatedStress2 !![σx, τ; τ, σy] θ 1 1
      = (σx + σy) / 2 - (σx - σy) / 2 * Real.cos (2 * θ)
        - τ * Real.sin (2 * θ) := by
  have hexpand : rotatedStress2 !![σx, τ; τ, σy] θ 1 1
      = σx * Real.sin θ ^ 2 - 2 * τ * Real.cos θ * Real.sin θ
        + σy * Real.cos θ ^ 2 := by
    simp [rotatedStress2, rotationMatrix2, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply]
    ring
  rw [hexpand, Real.cos_two_mul', Real.sin_two_mul]
  have hcs := Real.cos_sq_add_sin_sq θ
  linear_combination ((σx + σy) / 2) * hcs

/-- Transformation formula for the shear stress `τx'y'`. -/
lemma rotatedStress2_01 (σx σy τ θ : ℝ) :
    rotatedStress2 !![σx, τ; τ, σy] θ 0 1
      = -(σx - σy) / 2 * Real.sin (2 * θ) + τ * Real.cos (2 * θ) := by
  have hexpand : rotatedStress2 !![σx, τ; τ, σy] θ 0 1
      = -(σx - σy) * Real.cos θ * Real.sin θ
        + τ * (Real.cos θ ^ 2 - Real.sin θ ^ 2) := by
    simp [rotatedStress2, rotationMatrix2, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply]
    ring
  rw [hexpand, Real.cos_two_mul', Real.sin_two_mul]
  ring

/-- Mohr's circle center: the mean normal stress. -/
noncomputable def mohrMean (σx σy : ℝ) : ℝ := (σx + σy) / 2

/-- Squared Mohr's circle radius. -/
noncomputable def mohrRadiusSq (σx σy τ : ℝ) : ℝ := ((σx - σy) / 2) ^ 2 + τ ^ 2

/-- Mohr's circle equation: `(σx' - mean)² + τx'y'² = radius²` for every `θ`. -/
lemma mohr_circle (σx σy τ θ : ℝ) :
    (rotatedStress2 !![σx, τ; τ, σy] θ 0 0 - mohrMean σx σy) ^ 2
      + (rotatedStress2 !![σx, τ; τ, σy] θ 0 1) ^ 2
      = mohrRadiusSq σx σy τ := by
  rw [rotatedStress2_00, rotatedStress2_01]
  unfold mohrMean mohrRadiusSq
  have hcs := Real.cos_sq_add_sin_sq (2 * θ)
  linear_combination (((σx - σy) / 2) ^ 2 + τ ^ 2) * hcs

/-- Shear stress in the 1-3 principal plane at orientation `θ`. -/
noncomputable def principalPlaneShear (s₁ s₃ θ : ℝ) : ℝ :=
  -(s₁ - s₃) / 2 * Real.sin (2 * θ)

/-- In-plane maximum shear bound: `|τ(θ)| ≤ (s₁ - s₃)/2` for `s₁ ≥ s₃`. This is the maximum
over orientations within the 1-3 principal plane; the claim that the global 3D maximum shear is
attained in that plane is a documented consequence (the 3D extremum argument), not proved here. -/
lemma principalPlaneShear_bound (s₁ s₃ θ : ℝ) (hle : s₃ ≤ s₁) :
    |principalPlaneShear s₁ s₃ θ| ≤ (s₁ - s₃) / 2 := by
  have hneg : (-(s₁ - s₃) / 2 : ℝ) ≤ 0 := by linarith
  have habs : |(-(s₁ - s₃) / 2 : ℝ)| = (s₁ - s₃) / 2 := by
    rw [abs_of_nonpos hneg]; ring
  unfold principalPlaneShear
  calc |-(s₁ - s₃) / 2 * Real.sin (2 * θ)|
      = |-(s₁ - s₃) / 2| * |Real.sin (2 * θ)| := abs_mul _ _
    _ ≤ |-(s₁ - s₃) / 2| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
    _ = (s₁ - s₃) / 2 := by rw [mul_one, habs]

/-- The in-plane maximum shear is attained at `θ = π/4`. -/
lemma principalPlaneShear_max (s₁ s₃ : ℝ) (hle : s₃ ≤ s₁) :
    |principalPlaneShear s₁ s₃ (Real.pi / 4)| = (s₁ - s₃) / 2 := by
  have hneg : (-(s₁ - s₃) / 2 : ℝ) ≤ 0 := by linarith
  have habs : |(-(s₁ - s₃) / 2 : ℝ)| = (s₁ - s₃) / 2 := by
    rw [abs_of_nonpos hneg]; ring
  have harg : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
  unfold principalPlaneShear
  rw [harg, Real.sin_pi_div_two, mul_one, habs]

/-! ## D. Small strain, true strain, and true stress -/

/-- Displacement gradient: the Jacobian matrix of `u` at `x`, entry `(i, j)` being the
derivative of component `i` along coordinate direction `j`. -/
noncomputable def displacementGradient (u : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => deriv (fun t : ℝ => u (x + t • Pi.single j (1 : ℝ)) i) 0

/-- Small (infinitesimal) strain tensor `ε = (H + Hᵀ)/2`. -/
noncomputable def smallStrain (H : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / 2 : ℝ) • (H + Hᵀ)

/-- Small strain is symmetric. -/
lemma smallStrain_symmetric (H : Matrix (Fin 3) (Fin 3) ℝ) :
    (smallStrain H)ᵀ = smallStrain H := by
  unfold smallStrain
  rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

/-- Helper: derivative of an affine function at `0`. -/
lemma deriv_affine (a b : ℝ) : deriv (fun t : ℝ => a * t + b) 0 = a := by
  have h : HasDerivAt (fun t : ℝ => a * t + b) (a * 1) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_mul a).add_const b
  rw [h.deriv, mul_one]

/-- An affine displacement field with gradient `A` and offset `b`. -/
def affineDisplacement (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ)
    (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => (∑ j, A i j * x j) + b i

/-- The displacement gradient of an affine field is its coefficient matrix. -/
lemma displacementGradient_affine (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ)
    (x : Fin 3 → ℝ) : displacementGradient (affineDisplacement A b) x = A := by
  ext i j
  show deriv (fun t : ℝ => affineDisplacement A b (x + t • Pi.single j 1) i) 0
    = A i j
  have hfun : (fun t : ℝ => affineDisplacement A b (x + t • Pi.single j 1) i)
      = fun t => A i j * t + ((∑ k, A i k * x k) + b i) := by
    funext t
    simp only [affineDisplacement, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  rw [hfun]
  exact deriv_affine _ _

/-- A linear displacement `W *ᵥ x` is an affine field. -/
lemma mulVec_eq_affine (W : Matrix (Fin 3) (Fin 3) ℝ) :
    (fun x => W *ᵥ x) = affineDisplacement W 0 := by
  funext x i
  simp [affineDisplacement, Matrix.mulVec, dotProduct]

/-- Rigid-motion check: an infinitesimal rigid displacement `u x = W *ᵥ x` with skew `W`
has zero small strain. Finite rotations are not in scope (linearization). -/
lemma smallStrain_rigid (W : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ)
    (hW : Wᵀ = -W) :
    smallStrain (displacementGradient (fun x => W *ᵥ x) x) = 0 := by
  rw [mulVec_eq_affine, displacementGradient_affine]
  unfold smallStrain
  rw [hW, add_neg_cancel, smul_zero]

/-- Engineering shear strain `γ_xy = 2 ε_xy`. -/
def engineeringShear (ε : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := 2 * ε 0 1

/-- Simple shear field with amount `γ`: `(x₀ + γ x₁, x₁, x₂)`. -/
def simpleShearField (γ : ℝ) : (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  affineDisplacement !![1, γ, 0; 0, 1, 0; 0, 0, 1] 0

/-- Simple shear produces tensor shear `ε₀₁ = γ/2`, i.e. engineering shear `γ`. -/
lemma simpleShear_strain (γ : ℝ) (x : Fin 3 → ℝ) :
    smallStrain (displacementGradient (simpleShearField γ) x) 0 1 = γ / 2 := by
  unfold simpleShearField
  rw [displacementGradient_affine]
  unfold smallStrain
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
  ring

/-- Engineering shear of simple shear is exactly `γ`. -/
lemma simpleShear_engineering (γ : ℝ) (x : Fin 3 → ℝ) :
    engineeringShear (smallStrain (displacementGradient (simpleShearField γ) x))
      = γ := by
  unfold engineeringShear
  rw [simpleShear_strain]
  ring

/-- True (logarithmic) strain `ε_true = ln(1 + e)`. -/
noncomputable def trueStrain (e : ℝ) : ℝ := Real.log (1 + e)

/-- True strain vanishes at zero engineering strain. -/
lemma trueStrain_zero : trueStrain 0 = 0 := by
  simp [trueStrain]

/-- The true-strain argument is positive when `e > -1`. -/
lemma trueStrain_pos_arg (e : ℝ) (he : -1 < e) : (0 : ℝ) < 1 + e := by
  linarith

/-- Upper bound: `ln(1+e) ≤ e` for `e > -1`. -/
lemma trueStrain_le (e : ℝ) (he : -1 < e) : trueStrain e ≤ e := by
  unfold trueStrain
  have hpos : (0 : ℝ) < 1 + e := by linarith
  have h := Real.log_le_sub_one_of_pos hpos
  linarith [h]

/-- Strict upper bound: `ln(1+e) < e` for `e > -1`, `e ≠ 0`. -/
lemma trueStrain_lt (e : ℝ) (he : -1 < e) (hne : e ≠ 0) : trueStrain e < e := by
  unfold trueStrain
  have hpos : (0 : ℝ) < 1 + e := by linarith
  have hne1 : (1 + e : ℝ) ≠ 1 := by
    intro hcon
    apply hne
    linarith
  have h := Real.log_lt_sub_one_of_pos hpos hne1
  linarith [h]

/-- Lower bound: `e/(1+e) ≤ ln(1+e)` for `e > -1`. -/
lemma trueStrain_lower (e : ℝ) (he : -1 < e) : e / (1 + e) ≤ trueStrain e := by
  unfold trueStrain
  have hpos : (0 : ℝ) < 1 + e := by linarith
  have hne : (1 + e : ℝ) ≠ 0 := ne_of_gt hpos
  have hpos' : (0 : ℝ) < (1 + e)⁻¹ := by positivity
  have h := Real.log_le_sub_one_of_pos hpos'
  rw [Real.log_inv] at h
  have hinv : ((1 + e)⁻¹ - 1 : ℝ) = -(e / (1 + e)) := by
    field_simp
    ring
  rw [hinv] at h
  linarith [h]

/-- Engineering stress `s = F/A₀` (force over reference area). -/
noncomputable def engStress (F A₀ : ℝ) : ℝ := F / A₀

/-- True stress `σ = F/A` (force over current area). -/
noncomputable def trueStress (F A : ℝ) : ℝ := F / A

/-- Volume constancy (uniaxial incompressibility) gives `σ_true = s(1+e)`. Volume constancy
is a model hypothesis, not a theorem. -/
lemma trueStress_of_volumeConstancy (F A₀ A e : ℝ) (he : -1 < e)
    (hA₀ : A₀ ≠ 0) (hvol : A = A₀ / (1 + e)) :
    trueStress F A = engStress F A₀ * (1 + e) := by
  unfold trueStress engStress
  rw [hvol]
  have hne : (1 + e : ℝ) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 + e)
  field_simp

end Elasticity
