/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Geometry.M12Rotations

/-!
# Rotation checks

Concrete consumers of `MathlibExt.Geometry.M12Rotations`: the public
shape of both theorems for a generic orthogonal curve, and the
degenerate constant rotation `R(t) = 1`, whose angular-velocity matrix
is `0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here, apart from the
private constant-rotation helper used by the examples below.

## iii. Table of contents

- A. Public shape
- B. Constant rotation

## iv. References

- `MathlibExt.Geometry.M12Rotations`
-/

/-- Constant rotation `R(t) = 1`, used by the examples below. -/
private def constRot {n : ℕ} : ℝ → Matrix (Fin n) (Fin n) ℝ := fun _ => 1

/-- The public shape of skew-symmetry for a generic orthogonal curve. -/
example {n : ℕ} (R : ℝ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hOrth : ∀ s, R s * Matrix.transpose (R s) = 1)
    (hDiff : ∀ i k, DifferentiableAt ℝ (fun s => R s i k) t) :
    ∀ i j, (∑ k, deriv (fun s => R s i k) t * R t j k)
      = -(∑ k, deriv (fun s => R s j k) t * R t i k) :=
  EarthScience.angular_velocity_skew R t hOrth hDiff

/-- The public shape of the rotated-vector formula. -/
example {n : ℕ} (R : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) (t : ℝ) (i : Fin n)
    (hOrth : ∀ s, R s * Matrix.transpose (R s) = 1)
    (hDiff : ∀ i k, DifferentiableAt ℝ (fun s => R s i k) t) :
    deriv (fun s => Matrix.mulVec (R s) a i) t
      = ∑ j, (∑ k, deriv (fun s => R s i k) t * R t j k)
          * Matrix.mulVec (R t) a j :=
  EarthScience.rotated_vector_deriv R a t i hOrth hDiff

/-- Constant rotation: orthogonality and entrywise differentiability. -/
example {n : ℕ} (t : ℝ) :
    (∀ s, constRot (n := n) s * Matrix.transpose (constRot (n := n) s) = 1) ∧
    (∀ i k, DifferentiableAt ℝ (fun s => constRot (n := n) s i k) t) := by
  refine ⟨fun s => by simp [constRot], fun i k => ?_⟩
  simp only [constRot]
  exact differentiableAt_const _

/-- Constant rotation: the angular-velocity matrix is `0`. -/
example {n : ℕ} (t : ℝ) (i j : Fin n) :
    (∑ k, deriv (fun s => constRot (n := n) s i k) t * constRot (n := n) t j k) = 0 := by
  simp [constRot, deriv_const]

/-- Constant rotation: the rotated vector is constant, so `r' = W r`
holds with both sides `0` in the appropriate sense. -/
example {n : ℕ} (a : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    deriv (fun s => Matrix.mulVec (constRot (n := n) s) a i) t
      = ∑ j, (∑ k, deriv (fun s => constRot (n := n) s i k) t * constRot (n := n) t j k)
          * Matrix.mulVec (constRot (n := n) t) a j :=
  EarthScience.rotated_vector_deriv _ a t i
    (fun s => by simp [constRot])
    (fun i k => by simp only [constRot]; exact differentiableAt_const _)
