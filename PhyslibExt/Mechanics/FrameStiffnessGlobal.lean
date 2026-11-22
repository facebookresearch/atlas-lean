/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.BeamStiffness
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global planar frame stiffness by rotation congruence

## i. Overview

One planar frame element in the six-coordinate ordering
`(u1, v1, θ1, u2, v2, θ2)` of `Mechanics.EulerBernoulli.frameStiffness`,
with local axial direction given by global direction cosines
`(c, s)`. The global-to-local transform `frameRotation c s`
rotates the two translational coordinates at each end and
leaves the in-plane rotations unchanged; the global stiffness
is the congruence `K_global = Tᵀ * K_local * T`. The direction
cosines are arbitrary reals in the definitions; the unit-circle
hypothesis `c ^ 2 + s ^ 2 = 1` (an actual direction) is carried
exactly by the statements that need an orthogonal transform.
Symmetry, positive semidefiniteness, and the rigid-mode kernel
of the local element transport to the global element, and the
three global rigid modes (two translations and the rotation
about end 1) map to the local rigid modes.

## ii. Key results

- `Mechanics.EulerBernoulli.frameRotation` and
  `frameStiffnessGlobal`: the transform and the global
  stiffness.
- `Mechanics.EulerBernoulli.frameRotation_transpose_mul` and
  `frameRotation_mul_transpose`: orthogonality on the unit
  circle; `frameRotation_mulVec_round_trip`: coordinate round
  trips.
- `Mechanics.EulerBernoulli.frameStiffnessGlobal_quad_form`:
  stored-energy invariance under the congruence.
- `Mechanics.EulerBernoulli.frameStiffnessGlobal_transpose`,
  `frameStiffnessGlobal_posSemidef`, and
  `frameStiffnessGlobal_mulVec_eq_zero_iff`: symmetry,
  semidefiniteness, and the rigid-mode kernel of the global
  element.
- `Mechanics.EulerBernoulli.frameRotation_mulVec_globalTranslation`
  and `frameRotation_mulVec_globalRotation`: the global rigid
  modes in local coordinates.

## iii. Table of contents

- A. Transform and global stiffness
- B. Transport of symmetry, semidefiniteness, and kernel

## iv. References

- `PhyslibExt.Mechanics.BeamStiffness` for the local
  six-coordinate frame element, its quadratic form, and its
  rigid-mode kernel.
- R. C. Hibbeler, *Structural Analysis*, 10th edition,
  Pearson, 2017: the frame-element transformation matrix and
  the global stiffness `Tᵀ K T`.
-/

@[expose] public section

open Matrix

namespace Mechanics.EulerBernoulli

/-! ## A. Transform and global stiffness -/

/-- Global-to-local planar frame transform for one element whose
local axial direction has global direction cosines `(c, s)`.
At each end it maps global translations `(u, v)` to axial and
transverse components `(c*u + s*v, -s*u + c*v)` and leaves the
in-plane rotation coordinate unchanged. -/
noncomputable def frameRotation (c s : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![c, s, 0, 0, 0, 0;
    -s, c, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, c, s, 0;
    0, 0, 0, -s, c, 0;
    0, 0, 0, 0, 0, 1]

/-- Global frame-element stiffness by orthogonal congruence:
`K_global = Tᵀ * K_local * T`, with local displacements
`T *ᵥ d_global`. -/
noncomputable def frameStiffnessGlobal (EA EI L c s : ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  (frameRotation c s)ᵀ * frameStiffness EA EI L * frameRotation c s

/-- For direction cosines on the unit circle, the frame
transform is orthogonal in the transpose-left order. -/
theorem frameRotation_transpose_mul {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) :
    (frameRotation c s)ᵀ * frameRotation c s = 1 := by
  unfold frameRotation
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six] <;> linarith [hcs]

/-- For direction cosines on the unit circle, the frame
transform is orthogonal in the transpose-right order. -/
theorem frameRotation_mul_transpose {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) :
    frameRotation c s * (frameRotation c s)ᵀ = 1 := by
  unfold frameRotation
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six] <;> linarith [hcs]

/-- Coordinate round trips for the orthogonal frame transform. -/
theorem frameRotation_mulVec_round_trip {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (d : Fin 6 → ℝ) :
    (frameRotation c s)ᵀ *ᵥ (frameRotation c s *ᵥ d) = d ∧
      frameRotation c s *ᵥ ((frameRotation c s)ᵀ *ᵥ d) = d := by
  constructor
  · rw [Matrix.mulVec_mulVec, frameRotation_transpose_mul hcs, Matrix.one_mulVec]
  · rw [Matrix.mulVec_mulVec, frameRotation_mul_transpose hcs, Matrix.one_mulVec]

/-- Stored-energy invariance under the frame congruence: the
global quadratic form at `d` is the local quadratic form at the
local displacement `T *ᵥ d`. -/
theorem frameStiffnessGlobal_quad_form (EA EI L c s : ℝ)
    (d : Fin 6 → ℝ) :
    d ⬝ᵥ (frameStiffnessGlobal EA EI L c s *ᵥ d)
      = (frameRotation c s *ᵥ d)
          ⬝ᵥ (frameStiffness EA EI L *ᵥ (frameRotation c s *ᵥ d)) := by
  unfold frameStiffnessGlobal
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

/-! ## B. Transport of symmetry, semidefiniteness, and kernel -/

/-- Symmetry transport: if the supplied local frame matrix is
symmetric, its global congruence is symmetric. -/
private theorem frameStiffnessGlobal_transpose_of_local
    {EA EI L c s : ℝ}
    (hKsymm : (frameStiffness EA EI L)ᵀ = frameStiffness EA EI L) :
    (frameStiffnessGlobal EA EI L c s)ᵀ
      = frameStiffnessGlobal EA EI L c s := by
  simp [frameStiffnessGlobal, Matrix.transpose_mul,
    Matrix.transpose_transpose, hKsymm, Matrix.mul_assoc]

/-- Positive-semidefinite transport: if the supplied local
frame matrix is positive semidefinite, its global congruence is
positive semidefinite. -/
private theorem frameStiffnessGlobal_posSemidef_of_local
    {EA EI L c s : ℝ}
    (hKpsd : (frameStiffness EA EI L).PosSemidef) :
    (frameStiffnessGlobal EA EI L c s).PosSemidef := by
  unfold frameStiffnessGlobal
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hKpsd.conjTranspose_mul_mul_same _

/-- Kernel correspondence: for an orthogonal transform and a
supplied exact local rigid-mode kernel characterization, a
global displacement is in the global kernel exactly when its
local displacement is a local rigid mode. -/
private theorem frameStiffnessGlobal_mulVec_eq_zero_iff_of_local
    {EA EI L c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (hKkernel : ∀ x : Fin 6 → ℝ,
      frameStiffness EA EI L *ᵥ x = 0 ↔
        ∃ a b w : ℝ,
          x = a • ![1, 0, 0, 1, 0, 0]
            + b • ![0, 1, 0, 0, 1, 0]
            + w • ![0, 0, 1, 0, L, 1])
    (d : Fin 6 → ℝ) :
    frameStiffnessGlobal EA EI L c s *ᵥ d = 0 ↔
      ∃ a b w : ℝ,
        frameRotation c s *ᵥ d
          = a • ![1, 0, 0, 1, 0, 0]
            + b • ![0, 1, 0, 0, 1, 0]
            + w • ![0, 0, 1, 0, L, 1] := by
  have hTT : frameRotation c s * (frameRotation c s)ᵀ = 1 :=
    frameRotation_mul_transpose hcs
  unfold frameStiffnessGlobal
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have h2 : frameStiffness EA EI L *ᵥ (frameRotation c s *ᵥ d) = 0 := by
      have h0 : frameRotation c s *ᵥ ((frameRotation c s)ᵀ
          *ᵥ (frameStiffness EA EI L *ᵥ (frameRotation c s *ᵥ d))) = 0 := by
        rw [h]
        exact Matrix.mulVec_zero _
      rwa [Matrix.mulVec_mulVec, hTT, Matrix.one_mulVec] at h0
    exact (hKkernel _).mp h2
  · intro h
    have h2 : frameStiffness EA EI L *ᵥ (frameRotation c s *ᵥ d) = 0 :=
      (hKkernel _).mpr h
    rw [h2]
    exact Matrix.mulVec_zero _

/-- A global rigid translation maps to the corresponding
combination of the two local translation modes. -/
theorem frameRotation_mulVec_globalTranslation
    (c s a b : ℝ) :
    frameRotation c s *ᵥ ![a, b, 0, a, b, 0]
      = (c * a + s * b) • ![1, 0, 0, 1, 0, 0]
        + (-s * a + c * b) • ![0, 1, 0, 0, 1, 0] := by
  unfold frameRotation
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six]

/-- A global rigid rotation about end 1, for an element of
length `L` in direction `(c, s)`, maps to the local rigid
rotation mode. -/
theorem frameRotation_mulVec_globalRotation
    (L c s w : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    frameRotation c s *ᵥ ![0, 0, w, -L * s * w, L * c * w, w]
      = w • ![0, 0, 1, 0, L, 1] := by
  unfold frameRotation
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  · simp only [mulVec, dotProduct, Fin.reduceFinMk, of_apply, Fin.isValue,
      cons_val', cons_val_fin_one, cons_val, cons_val_one, cons_val_zero,
      neg_mul, Fin.sum_univ_six, mul_zero, add_zero, zero_mul, mul_neg,
      zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [mulVec, dotProduct, Fin.reduceFinMk, of_apply, Fin.isValue,
      cons_val', cons_val_fin_one, cons_val, cons_val_one, cons_val_zero,
      neg_mul, Fin.sum_univ_six, mul_zero, add_zero, zero_mul, mul_neg,
      neg_neg, zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, Pi.smul_apply,
      smul_eq_mul]
    have h2 : L * w * (c ^ 2 + s ^ 2) = L * w := by rw [hcs]; ring
    linarith [h2]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six]

/-- Direct symmetry of the global frame stiffness. -/
theorem frameStiffnessGlobal_transpose (EA EI L c s : ℝ) :
    (frameStiffnessGlobal EA EI L c s)ᵀ
      = frameStiffnessGlobal EA EI L c s := by
  exact frameStiffnessGlobal_transpose_of_local (frameStiffness_transpose EA EI L)

/-- Direct positive semidefiniteness of the global frame
stiffness for positive axial rigidity, flexural rigidity, and
length. -/
theorem frameStiffnessGlobal_posSemidef {EA EI L c s : ℝ}
    (hEA : 0 < EA) (hEI : 0 < EI) (hL : 0 < L) :
    (frameStiffnessGlobal EA EI L c s).PosSemidef := by
  exact frameStiffnessGlobal_posSemidef_of_local (frameStiffness_posSemidef hEA hEI hL)

/-- Direct kernel correspondence for the global frame stiffness:
for positive rigidities and length and an orthogonal transform,
a global displacement is in the kernel exactly when its local
displacement is a local rigid mode. -/
theorem frameStiffnessGlobal_mulVec_eq_zero_iff
    {EA EI L c s : ℝ} (hEA : 0 < EA) (hEI : 0 < EI) (hL : 0 < L)
    (hcs : c ^ 2 + s ^ 2 = 1) (d : Fin 6 → ℝ) :
    frameStiffnessGlobal EA EI L c s *ᵥ d = 0 ↔
      ∃ a b w : ℝ,
        frameRotation c s *ᵥ d
          = a • ![1, 0, 0, 1, 0, 0]
            + b • ![0, 1, 0, 0, 1, 0]
            + w • ![0, 0, 1, 0, L, 1] := by
  exact frameStiffnessGlobal_mulVec_eq_zero_iff_of_local hcs
    (fun x => frameStiffness_mulVec_eq_zero_iff hEA hEI hL x) d

end Mechanics.EulerBernoulli
