/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Column buckling: explicit support-specific eigenpairs

## i. Overview

Explicit eigenfunctions of the fourth-order Euler column equation
`EI * w'''' + P * w'' = 0` for columns of length `L` with flexural
rigidity `EI` under axial load `P`, verified together with their support
conditions. These are single explicit eigenpairs: no lowest-mode,
completeness, or global-minimum claim over a space of admissible
displacements is made here.

## ii. Key results

- `Elasticity.clampedClamped_eigenpair`: `w = 1 - cos (2πx / L)` at
  `P = 4π²EI / L²` satisfies the column equation and the clamped
  conditions `w = w' = 0` at both ends, with midspan value `2`
  (`Elasticity.clampedClampedMode_midspan`).

## iii. Table of contents

- A. The clamped-clamped mode

## iv. References

- The Euler column equation and its support-dependent eigenvalues are
  standard in mechanics of materials; the derivative computations use
  `Real.hasDerivAt_sin`, `Real.hasDerivAt_cos`, and Mathlib's
  `iteratedDeriv` API.

## A. The clamped-clamped mode

-/

@[expose] public section

namespace Elasticity

/-- The clamped-clamped column mode `w(x) = 1 - cos (2πx / L)` on a column
of length `L`. This is one explicit buckling eigenfunction; nothing here
claims it is the lowest mode or part of a complete set. -/
noncomputable def clampedClampedMode (L : ℝ) (x : ℝ) : ℝ :=
  1 - Real.cos (2 * Real.pi * x / L)

/-- Derivative of the linear phase `2πx / L`. -/
private lemma hasDerivAt_phase {L : ℝ} (x : ℝ) :
    HasDerivAt (fun x : ℝ => 2 * Real.pi * x / L) (2 * Real.pi / L) x := by
  have h := (hasDerivAt_id x).const_mul (2 * Real.pi / L)
  rw [mul_one] at h
  have heq : (fun x : ℝ => 2 * Real.pi * x / L)
      = fun x : ℝ => (2 * Real.pi / L) * x := by
    funext y
    ring
  rwa [heq]

/-- The clamped-clamped mode vanishes at the left support. -/
lemma clampedClampedMode_zero (L : ℝ) : clampedClampedMode L 0 = 0 := by
  simp [clampedClampedMode]

/-- The clamped-clamped mode vanishes at the right support. -/
lemma clampedClampedMode_length {L : ℝ} (hL : L ≠ 0) :
    clampedClampedMode L L = 0 := by
  have hph : 2 * Real.pi * L / L = 2 * Real.pi := by field_simp
  simp only [clampedClampedMode, hph, Real.cos_two_pi, sub_self]

/-- Nonzero midspan displacement: the clamped-clamped mode takes the
value `2` at `x = L / 2`. -/
lemma clampedClampedMode_midspan {L : ℝ} (hL : L ≠ 0) :
    clampedClampedMode L (L / 2) = 2 := by
  have hph : 2 * Real.pi * (L / 2) / L = Real.pi := by
    field_simp
  simp only [clampedClampedMode, hph, Real.cos_pi]
  norm_num

/-- First derivative of the clamped-clamped mode. -/
lemma deriv_clampedClampedMode {L : ℝ} (hL : L ≠ 0) :
    deriv (clampedClampedMode L) =
      fun x => (2 * Real.pi / L) * Real.sin (2 * Real.pi * x / L) := by
  have _ : L ≠ 0 := hL
  funext x
  have h := ((hasDerivAt_phase (L := L) x).cos.const_sub 1).deriv
  show deriv (fun x : ℝ => 1 - Real.cos (2 * Real.pi * x / L)) x = _
  rw [h]
  ring

/-- Second derivative of the clamped-clamped mode. -/
lemma iteratedDeriv_two_clampedClampedMode {L : ℝ} (hL : L ≠ 0) (x : ℝ) :
    iteratedDeriv 2 (clampedClampedMode L) x =
      (2 * Real.pi / L) ^ 2 * Real.cos (2 * Real.pi * x / L) := by
  have hstep : iteratedDeriv 2 (clampedClampedMode L) x
      = deriv (deriv (clampedClampedMode L)) x := by
    have h := congrFun (iteratedDeriv_succ (n := 1) (f := clampedClampedMode L)) x
    rwa [iteratedDeriv_one] at h
  rw [hstep, deriv_clampedClampedMode hL]
  have h :=
    ((hasDerivAt_phase (L := L) x).sin.const_mul (2 * Real.pi / L)).deriv
  rw [h]
  ring

/-- Fourth derivative of the clamped-clamped mode. -/
lemma iteratedDeriv_four_clampedClampedMode {L : ℝ} (hL : L ≠ 0) (x : ℝ) :
    iteratedDeriv 4 (clampedClampedMode L) x =
      -((2 * Real.pi / L) ^ 4) * Real.cos (2 * Real.pi * x / L) := by
  have h2 : iteratedDeriv 2 (clampedClampedMode L)
      = fun x => (2 * Real.pi / L) ^ 2 * Real.cos (2 * Real.pi * x / L) :=
    funext (iteratedDeriv_two_clampedClampedMode hL)
  have h3 : iteratedDeriv 3 (clampedClampedMode L)
      = fun x => -((2 * Real.pi / L) ^ 3) * Real.sin (2 * Real.pi * x / L) := by
    funext y
    have hstep : iteratedDeriv 3 (clampedClampedMode L) y
        = deriv (iteratedDeriv 2 (clampedClampedMode L)) y :=
      congrFun (iteratedDeriv_succ (n := 2) (f := clampedClampedMode L)) y
    rw [hstep, h2]
    have h :=
      ((hasDerivAt_phase (L := L) y).cos.const_mul ((2 * Real.pi / L) ^ 2)).deriv
    rw [h]
    ring
  have hstep : iteratedDeriv 4 (clampedClampedMode L) x
      = deriv (iteratedDeriv 3 (clampedClampedMode L)) x :=
    congrFun (iteratedDeriv_succ (n := 3) (f := clampedClampedMode L)) x
  rw [hstep, h3]
  have h :=
    ((hasDerivAt_phase (L := L) x).sin.const_mul (-((2 * Real.pi / L) ^ 3))).deriv
  rw [h]
  ring

/-- The clamped-clamped eigenpair: with axial load `P = 4π²EI / L²`, the
mode `w = 1 - cos (2πx / L)` satisfies the fourth-order Euler column
equation `EI * w'''' + P * w'' = 0` at every `x`, together with the
clamped displacement and slope conditions `w = w' = 0` at both supports.
This records one explicit eigenpair, not a lowest-mode or completeness
claim. -/
theorem clampedClamped_eigenpair {EI L : ℝ} (hL : 0 < L) :
    (∀ x : ℝ, EI * iteratedDeriv 4 (clampedClampedMode L) x +
        (4 * Real.pi ^ 2 * EI / L ^ 2) *
          iteratedDeriv 2 (clampedClampedMode L) x = 0) ∧
      clampedClampedMode L 0 = 0 ∧ clampedClampedMode L L = 0 ∧
        deriv (clampedClampedMode L) 0 = 0 ∧
          deriv (clampedClampedMode L) L = 0 := by
  have hLne : L ≠ 0 := ne_of_gt hL
  refine ⟨?_, clampedClampedMode_zero L, clampedClampedMode_length hLne, ?_, ?_⟩
  · intro x
    rw [iteratedDeriv_four_clampedClampedMode hLne,
      iteratedDeriv_two_clampedClampedMode hLne]
    field_simp
    ring
  · rw [deriv_clampedClampedMode hLne]
    simp
  · rw [deriv_clampedClampedMode hLne]
    show (2 * Real.pi / L) * Real.sin (2 * Real.pi * L / L) = 0
    have hph : 2 * Real.pi * L / L = 2 * Real.pi := by field_simp
    rw [hph, Real.sin_two_pi, mul_zero]

end Elasticity
