/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Unit-quaternion rotation action

## i. Overview

For a unit real quaternion `q`, conjugation `v ↦ q * v * star q` restricts
to a real linear isometry of the pure imaginary quaternions. In the explicit
basis `i, j, k`, its matrix lies in the existing
`Matrix.specialOrthogonalGroup (Fin 3) ℝ` carrier; no new rotation type is
introduced.

The pure imaginary quaternions are the kernel of the real-part map
`QuaternionAlgebra.reₗ`; coordinate `a : Fin 3` of a quaternion is
`![x.imI, x.imJ, x.imK] a`, and the basis vector with index `b` is
`![i, j, k] b` with `i = ⟨0, 1, 0, 0⟩`, `j = ⟨0, 0, 1, 0⟩`,
`k = ⟨0, 0, 0, 1⟩`.

## ii. Key results

- `QuaternionRotation.exists_linearIsometry_conj`: conjugation by a unit
  quaternion is a linear isometry of `pureIm`.
- `QuaternionRotation.rotMatrix_mulVec`: `rotMatrix q` represents that
  conjugation in the explicit coordinates.
- `QuaternionRotation.unitaryHomSpecialOrthogonalGroup`: the packaged
  monoid homomorphism from `unitary ℍ` into
  `Matrix.specialOrthogonalGroup (Fin 3) ℝ`.
- `QuaternionRotation.rotMatrix_eq_one_iff`: on unit quaternions, the
  rotation matrix is the identity exactly at `q = 1` and `q = -1`.

## iii. Table of contents

- A. Pure imaginary quaternions and coordinates
- B. The rotation matrix and its group properties
- C. Fixtures
- D. Kernel and sign invariance

## iv. References

- Mathlib's quaternion, unitary-group, and matrix-determinant APIs.
-/

@[expose] public section

open Quaternion

namespace QuaternionRotation

/-- Pure imaginary quaternions: the kernel of the real part. -/
def pureIm : Submodule ℝ ℍ := LinearMap.ker (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1))

/-- Explicit coordinates of a quaternion in the imaginary basis `i, j, k`. -/
def imCoords (x : ℍ) : Fin 3 → ℝ := ![x.imI, x.imJ, x.imK]

/-- Explicit imaginary basis vectors `i, j, k`, indexed by `Fin 3`. -/
def imBasis : Fin 3 → ℍ := ![⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

/-- The matrix of `v ↦ q * v * star q` in the explicit basis `i, j, k`:
column `b` holds the coordinates of the image of basis vector `b`. -/
def rotMatrix (q : ℍ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => imCoords (q * imBasis b * star q) a

private theorem re_conj (q v : ℍ) : (q * v * star q).re = normSq q * v.re := by
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star,
    Quaternion.normSq_def']
  ring

private theorem normSq_eq_one_of_norm {q : ℍ} (hq : ‖q‖ = 1) : normSq q = 1 := by
  rw [Quaternion.normSq_eq_norm_mul_self, hq, mul_one]

private theorem det_rotMatrix_general (q : ℍ) : (rotMatrix q).det = (normSq q) ^ 3 := by
  simp [rotMatrix, imCoords, imBasis, Matrix.det_fin_three, Quaternion.normSq_def']
  ring

/-- For every quaternion `q`, `(rotMatrix q)ᵀ * rotMatrix q = (normSq q) ^ 2 • 1`, that is
`Rᵀ R = |q|⁴ 1`; no unit hypothesis is needed. -/
theorem rotMatrix_transpose_mul_self (q : ℍ) :
    Matrix.transpose (rotMatrix q) * rotMatrix q
      = (normSq q) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rotMatrix, imCoords, imBasis, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_three, Quaternion.normSq_def', Function.swap] <;>
    ring

/-- For unit `q`, conjugation `v ↦ q * v * star q` restricts to a real linear
isometry of the pure imaginary quaternions. -/
theorem exists_linearIsometry_conj {q : ℍ} (hq : ‖q‖ = 1) :
    ∃ f : pureIm →ₗᵢ[ℝ] pureIm, ∀ v : pureIm, (f v : ℍ) = q * (v : ℍ) * star q := by
  have hpres : ∀ x ∈ pureIm, (LinearMap.mulLeftRight ℝ (q, star q)) x ∈ pureIm := by
    intro x hx
    have hx0 : x.re = 0 := by simpa [pureIm] using hx
    have h : (q * x * star q).re = 0 := by rw [re_conj, hx0, mul_zero]
    have h2 : (LinearMap.mulLeftRight ℝ (q, star q) x).re = 0 := by
      simpa [LinearMap.mulLeftRight_apply] using h
    simpa [pureIm] using h2
  let L := (LinearMap.mulLeftRight ℝ (q, star q)).restrict hpres
  have hnorm : ∀ v : pureIm, ‖L v‖ = ‖v‖ := by
    intro v
    have h1 : ((L v : pureIm) : ℍ) = q * (v : ℍ) * star q := by
      simp [L, LinearMap.mulLeftRight_apply]
    have h2 : ‖L v‖ = ‖((L v : pureIm) : ℍ)‖ := rfl
    have h3 : ‖(v : pureIm)‖ = ‖((v : pureIm) : ℍ)‖ := rfl
    rw [h2, h3, h1]
    simp [norm_mul, hq]
  refine ⟨⟨L, hnorm⟩, ?_⟩
  intro v
  simp [L, LinearMap.mulLeftRight_apply]

/-- `rotMatrix q` represents conjugation by `q` on pure imaginary quaternions
in the explicit coordinates. -/
theorem rotMatrix_mulVec {q : ℍ} {v : ℍ} (hv : v ∈ pureIm) :
    (rotMatrix q).mulVec (imCoords v) = imCoords (q * v * star q) := by
  have hv0 : v.re = 0 := by simpa [pureIm] using hv
  ext a
  fin_cases a <;>
    simp [rotMatrix, imCoords, imBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv0] <;>
    ring

/-- Determinant one. -/
theorem det_rotMatrix {q : ℍ} (hq : ‖q‖ = 1) : (rotMatrix q).det = 1 := by
  have hN : normSq q = 1 := normSq_eq_one_of_norm hq
  have hdet : (rotMatrix q).det = (normSq q) ^ 3 := det_rotMatrix_general q
  rw [hdet, hN, one_pow]

/-- The matrix lies in the existing special orthogonal group carrier. -/
theorem rotMatrix_mem_specialOrthogonalGroup {q : ℍ} (hq : ‖q‖ = 1) :
    rotMatrix q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have hN : normSq q = 1 := normSq_eq_one_of_norm hq
  have hdet : (rotMatrix q).det = 1 := det_rotMatrix hq
  have hort : Matrix.transpose (rotMatrix q) * rotMatrix q = 1 := by
    have hgen := rotMatrix_transpose_mul_self q
    rw [hgen, hN, one_pow, one_smul]
  have horth : rotMatrix q ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff']
    exact hort
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨horth, hdet⟩

/-- Multiplicativity: `R (p * q) = R p * R q`. -/
theorem rotMatrix_mul {p q : ℍ} :
    rotMatrix (p * q) = rotMatrix p * rotMatrix q := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rotMatrix, imCoords, imBasis, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

/-- The rotation matrix of the identity quaternion is the identity matrix. -/
private theorem rotMatrix_one : rotMatrix 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rotMatrix, imCoords, imBasis]

/-- The packaged rotation action: unit quaternions act by conjugation on
pure imaginary quaternions, packaged as a monoid homomorphism into the
existing `Matrix.specialOrthogonalGroup (Fin 3) ℝ` carrier. -/
noncomputable def unitaryHomSpecialOrthogonalGroup :
    unitary ℍ →* Matrix.specialOrthogonalGroup (Fin 3) ℝ where
  toFun := fun u => ⟨rotMatrix (u : ℍ),
    rotMatrix_mem_specialOrthogonalGroup (CStarRing.norm_coe_unitary u)⟩
  map_one' := by
    apply Subtype.ext
    simp only
    have h1 : ((1 : unitary ℍ) : ℍ) = 1 := rfl
    rw [h1]
    exact rotMatrix_one
  map_mul' := fun u v => by
    apply Subtype.ext
    simp only
    have hmul : ((u * v : unitary ℍ) : ℍ) = (u : ℍ) * (v : ℍ) := rfl
    rw [hmul]
    exact rotMatrix_mul

/-- The underlying matrix of the packaged rotation action is `rotMatrix`. -/
@[simp] theorem coe_unitaryHomSpecialOrthogonalGroup (u : unitary ℍ) :
    (unitaryHomSpecialOrthogonalGroup u : Matrix (Fin 3) (Fin 3) ℝ) =
      rotMatrix (u : ℍ) :=
  rfl

/-- Packaged: a monoid homomorphism from unit quaternions into the existing
`Matrix.specialOrthogonalGroup (Fin 3) ℝ` whose underlying matrix is
`rotMatrix`, witnessed by `unitaryHomSpecialOrthogonalGroup`. -/
theorem exists_unitary_hom_specialOrthogonalGroup :
    ∃ R : unitary ℍ →* Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ u : unitary ℍ, (R u : Matrix (Fin 3) (Fin 3) ℝ) = rotMatrix (u : ℍ) :=
  ⟨unitaryHomSpecialOrthogonalGroup,
    fun u => coe_unitaryHomSpecialOrthogonalGroup u⟩

/-- Fixture: the quarter turn `(1 + i) / √2` about the `i` axis is a unit
quaternion whose rotation matrix is the nonidentity matrix sending `j ↦ k`,
`k ↦ -j`. -/
theorem quarterTurn_rotMatrix :
    ‖(⟨√2 / 2, √2 / 2, 0, 0⟩ : ℍ)‖ = 1 ∧
      rotMatrix ⟨√2 / 2, √2 / 2, 0, 0⟩ = !![1, 0, 0; 0, 0, -1; 0, 1, 0] ∧
      rotMatrix ⟨√2 / 2, √2 / 2, 0, 0⟩ ≠ 1 := by
  have hN : Quaternion.normSq (⟨√2 / 2, √2 / 2, 0, 0⟩ : ℍ) = 1 := by
    rw [Quaternion.normSq_def']
    simp only
    have h2sq : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hhalf : (√2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, h2sq]
      norm_num
    rw [hhalf]
    norm_num
  have hNorm : ‖(⟨√2 / 2, √2 / 2, 0, 0⟩ : ℍ)‖ = 1 := by
    have hmul : ‖(⟨√2 / 2, √2 / 2, 0, 0⟩ : ℍ)‖ * ‖(⟨√2 / 2, √2 / 2, 0, 0⟩ : ℍ)‖ = 1 := by
      rw [← Quaternion.normSq_eq_norm_mul_self, hN]
    have hx : 0 ≤ ‖(⟨√2 / 2, √2 / 2, 0, 0⟩ : ℍ)‖ := norm_nonneg _
    have h1 := mul_self_eq_one_iff.mp hmul
    cases h1 with
    | inl h => exact h
    | inr h =>
      rw [h] at hx
      norm_num at hx
  have h2mul : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hmulhalf : √2 / 2 * (√2 / 2) = 1 / 2 := by
    rw [div_mul_div_comm, h2mul]
    norm_num
  have hMat : rotMatrix (⟨√2 / 2, √2 / 2, 0, 0⟩ : ℍ) = !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [rotMatrix, imCoords, imBasis, hmulhalf] <;>
      norm_num
  have hNe : rotMatrix (⟨√2 / 2, √2 / 2, 0, 0⟩ : ℍ) ≠ 1 := by
    rw [hMat]
    intro h
    have h11 := congrArg (fun M => M 1 1) h
    simp at h11
  exact ⟨hNorm, hMat, hNe⟩

/-- Invalid input: the nonunit quaternion `2` is not a unit quaternion and its
conjugation matrix is not in the special orthogonal group. -/
theorem two_not_rotation :
    (2 : ℍ) ∉ unitary ℍ ∧ rotMatrix 2 ∉ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have hNotUnit : (2 : ℍ) ∉ unitary ℍ := by
    intro h
    have hn : ‖(2 : ℍ)‖ = 1 := CStarRing.norm_of_mem_unitary h
    have h2 : ‖(2 : ℍ)‖ = 2 := by
      have : (2 : ℍ) = ((2 : ℝ) : ℍ) := rfl
      rw [this, Quaternion.norm_coe]
      norm_num
    rw [h2] at hn
    norm_num at hn
  have hN2 : normSq (2 : ℍ) = 4 := by
    have hcoe : (2 : ℍ) = ((2 : ℝ) : ℍ) := rfl
    rw [hcoe, Quaternion.normSq_coe]
    norm_num
  have hdet2 : (rotMatrix 2).det = 64 := by
    rw [det_rotMatrix_general, hN2]
    norm_num
  have hNotSO : rotMatrix 2 ∉ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    intro hMem
    have hdet1 : (rotMatrix 2).det = 1 :=
      (Matrix.mem_specialOrthogonalGroup_iff.mp hMem).2
    rw [hdet2] at hdet1
    norm_num at hdet1
  exact ⟨hNotUnit, hNotSO⟩

/-- Kernel on unit quaternions: `rotMatrix q` is the identity matrix
exactly when `q = 1` or `q = -1`. -/
theorem rotMatrix_eq_one_iff {q : ℍ} (hq : ‖q‖ = 1) :
    rotMatrix q = 1 ↔ q = 1 ∨ q = -1 := by
  constructor
  · intro h
    have e00 : rotMatrix q 0 0 = q.re^2 + q.imI^2 - q.imJ^2 - q.imK^2 := by
      simp [rotMatrix, imCoords, imBasis]
      ring
    have e11 : rotMatrix q 1 1 = q.re^2 - q.imI^2 + q.imJ^2 - q.imK^2 := by
      simp [rotMatrix, imCoords, imBasis]
      ring
    have h00 : q.re^2 + q.imI^2 - q.imJ^2 - q.imK^2 = 1 := by
      have h0 := congrFun (congrFun h (0 : Fin 3)) (0 : Fin 3)
      rw [e00] at h0
      simpa using h0
    have h11 : q.re^2 - q.imI^2 + q.imJ^2 - q.imK^2 = 1 := by
      have h1 := congrFun (congrFun h (1 : Fin 3)) (1 : Fin 3)
      rw [e11] at h1
      simpa using h1
    have hnorm : q.re^2 + q.imI^2 + q.imJ^2 + q.imK^2 = 1 := by
      have hmul : ‖q‖ * ‖q‖ = 1 := by rw [hq]; norm_num
      have hN : Quaternion.normSq q = 1 := by
        rw [Quaternion.normSq_eq_norm_mul_self, hmul]
      rw [Quaternion.normSq_def'] at hN
      linarith
    have hJ2 : q.imJ^2 = 0 := by
      have hC := sq_nonneg q.imJ
      have hD := sq_nonneg q.imK
      have hCD : q.imJ^2 + q.imK^2 = 0 := by linarith
      linarith
    have hK2 : q.imK^2 = 0 := by
      have hC := sq_nonneg q.imJ
      have hD := sq_nonneg q.imK
      have hCD : q.imJ^2 + q.imK^2 = 0 := by linarith
      linarith
    have hJ0 : q.imJ = 0 := sq_eq_zero_iff.mp hJ2
    have hK0 : q.imK = 0 := sq_eq_zero_iff.mp hK2
    have hI2 : q.imI^2 = 0 := by
      have hB := sq_nonneg q.imI
      have hD := sq_nonneg q.imK
      linarith
    have hI0 : q.imI = 0 := sq_eq_zero_iff.mp hI2
    have hA : q.re^2 = 1 := by linarith
    rcases sq_eq_one_iff.mp hA with hr | hr
    · left
      rw [Quaternion.ext_iff]
      simp [hr, hI0, hJ0, hK0]
    · right
      rw [Quaternion.ext_iff]
      simp [hr, hI0, hJ0, hK0]
  · rintro (rfl | rfl)
    · ext a b
      fin_cases a <;> fin_cases b <;> simp [rotMatrix, imCoords, imBasis]
    · ext a b
      fin_cases a <;> fin_cases b <;> simp [rotMatrix, imCoords, imBasis]

/-- Sign invariance: `q` and `-q` determine the same rotation matrix,
for every quaternion `q`. -/
theorem rotMatrix_neg (q : ℍ) : rotMatrix (-q) = rotMatrix q := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [rotMatrix, imCoords, imBasis]

/-- The quaternions `1` and `-1` determine the same rotation matrix. -/
theorem rotMatrix_one_eq_rotMatrix_neg_one :
    rotMatrix (1 : ℍ) = rotMatrix (-1 : ℍ) := by
  exact (rotMatrix_neg 1).symm

/-- The quarter turn about the `i` axis is not the identity rotation. -/
theorem quarterTurn_rotMatrix_ne_one :
    rotMatrix ⟨√2 / 2, √2 / 2, 0, 0⟩ ≠ 1 := by
  exact quarterTurn_rotMatrix.2.2

end QuaternionRotation
