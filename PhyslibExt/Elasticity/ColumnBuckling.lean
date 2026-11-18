/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Column buckling: explicit eigenpairs and the pinned-pinned threshold

## i. Overview

Explicit eigenfunctions of the fourth-order Euler column equation
`EI * w'''' + P * w'' = 0` for columns of length `L` with flexural
rigidity `EI` under axial load `P`, verified together with their support
conditions. These are single explicit eigenpairs: no lowest-mode,
completeness, or global-minimum claim over a space of admissible
displacements is made here.

Section C is the pinned-pinned energy threshold. For a `C^2` deflection
represented on `[0, L]` by derivative fields `w'` and `w''` and vanishing
at both ends, the slope energy obeys
`∫ (w')^2 ≤ (L / π)^2 * ∫ (w'')^2`; hence the quadratic energy is
positive below the Euler load `π^2 * EI / L^2` for deflections that are
nonzero somewhere on the interval. The pinned sine mode gives equality
at that load and negative quadratic energy above it.

## ii. Key results

- `Elasticity.clampedClamped_eigenpair`: for positive flexural
  rigidity, `w = 1 - cos (2πx / L)` at `P = 4π²EI / L²` satisfies the
  column equation and the clamped conditions `w = w' = 0` at both
  ends, with midspan value `2`
  (`Elasticity.clampedClampedMode_midspan`). The unrestricted algebraic
  identity behind it, valid for every real `EI`, is
  `Elasticity.clampedClamped_columnEquation`.
- `Elasticity.clampedFree_eigenpair`: for positive flexural rigidity,
  `w = 1 - cos (πx / (2L))` at `P = π²EI / (4L²)` satisfies the column
  equation with the clamped-free support and natural conditions, with
  tip value `1` (`Elasticity.clampedFreeMode_tip`).
- `Elasticity.integral_deriv_sq_le`: for a pinned-pinned deflection
  vanishing at both ends, `∫ (w')^2 ≤ (L / π)^2 * ∫ (w'')^2`.
- `Elasticity.quadratic_energy_pos_of_lt`: below `π^2 * EI / L^2`, every
  such deflection that is nonzero somewhere on `[0, L]` has strictly
  positive quadratic energy; `pinnedMode_energy_eq_zero` and
  `pinnedMode_energy_neg` evaluate the sine mode at and above the load.

## iii. Table of contents

- A. The clamped-clamped mode
- B. The clamped-free mode
- C. The pinned-pinned energy threshold

## iv. References

- J. E. Shigley, C. R. Mischke, *Mechanical Engineering Design*
  (McGraw-Hill): columns and the Euler column formula, including
  end-condition-dependent effective lengths; the fixed-fixed (both ends
  clamped) case has theoretical effective-length factor `K = 1/2`, so
  the first fixed-fixed buckling load is `4π²EI / L²`, matching the
  eigenpair verified here. The pinned-pinned case has `K = 1`, giving the
  threshold `π^2 * EI / L^2` used in Section C. Authorship across editions changes
  (Shigley-Mischke 6th ed., c2001; later editions add Budynas and
  Nisbett), so the title and original authors are cited without an
  edition claim.
- The derivative computations use `Real.hasDerivAt_sin`,
  `Real.hasDerivAt_cos`, and Mathlib's `iteratedDeriv` API.

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

/-- Unrestricted algebraic form of the clamped-clamped column identity:
with axial load `P = 4π²EI / L²`, the mode `w = 1 - cos (2πx / L)`
satisfies the fourth-order Euler column equation
`EI * w'''' + P * w'' = 0` at every `x`, together with the clamped
displacement and slope conditions `w = w' = 0` at both supports, for
every real `EI` (the identity is linear in `EI`; the degenerate case
`EI = 0` makes both sides of the equation zero and carries no column
mechanics). This records one explicit eigenpair, not a lowest-mode or
completeness claim. -/
lemma clampedClamped_columnEquation {EI L : ℝ} (hL : 0 < L) :
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

/-- The clamped-clamped Euler column eigenpair: for positive flexural
rigidity `EI` and column length `L`, `w = 1 - cos (2πx / L)` at axial
load `P = 4π²EI / L²` is a buckling eigenfunction of a fixed-fixed
column (both ends clamped). The factor `4` against the pinned-pinned
load `π²EI / L²` is the standard fixed-fixed Euler result (effective
length `L / 2`); see the module references. One explicit eigenpair, not
a lowest-mode or completeness claim. -/
theorem clampedClamped_eigenpair {EI L : ℝ} (hEI : 0 < EI) (hL : 0 < L) :
    (∀ x : ℝ, EI * iteratedDeriv 4 (clampedClampedMode L) x +
        (4 * Real.pi ^ 2 * EI / L ^ 2) *
          iteratedDeriv 2 (clampedClampedMode L) x = 0) ∧
      clampedClampedMode L 0 = 0 ∧ clampedClampedMode L L = 0 ∧
        deriv (clampedClampedMode L) 0 = 0 ∧
          deriv (clampedClampedMode L) L = 0 :=
  clampedClamped_columnEquation hL

/-! ## B. The clamped-free mode -/

/-- The clamped-free column mode `w(x) = 1 - cos (πx / (2L))` on a column
of length `L`, clamped at `x = 0` and free at `x = L`. This is one
explicit buckling eigenfunction; nothing here claims it is the lowest
mode or part of a complete set. -/
noncomputable def clampedFreeMode (L : ℝ) (x : ℝ) : ℝ :=
  1 - Real.cos (Real.pi * x / (2 * L))

/-- The clamped-free mode vanishes at the clamped support. -/
lemma clampedFreeMode_zero (L : ℝ) : clampedFreeMode L 0 = 0 := by
  simp [clampedFreeMode]

/-- Nonzero tip displacement: the clamped-free mode takes the value `1`
at the free end `x = L`. -/
lemma clampedFreeMode_tip {L : ℝ} (hL : L ≠ 0) :
    clampedFreeMode L L = 1 := by
  unfold clampedFreeMode
  have hphase : Real.pi * L / (2 * L) = Real.pi / 2 := by
    field_simp
  rw [hphase, Real.cos_pi_div_two]
  ring

/-- First derivative of the clamped-free mode. -/
lemma deriv_clampedFreeMode {L : ℝ} (hL : L ≠ 0) :
    deriv (clampedFreeMode L) =
      fun x => (Real.pi / (2 * L)) * Real.sin (Real.pi * x / (2 * L)) := by
  have _ : L ≠ 0 := hL
  funext x
  have hinner : HasDerivAt (fun x : ℝ => Real.pi * x / (2 * L)) (Real.pi / (2 * L)) x := by
    have hfun : (fun x : ℝ => Real.pi * x / (2 * L)) = fun x => (Real.pi / (2 * L)) * x := by
      funext y
      ring
    rw [hfun]
    exact hasDerivAt_const_mul _
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (Real.pi * x / (2 * L)))
      (-Real.sin (Real.pi * x / (2 * L)) * (Real.pi / (2 * L))) x :=
    hinner.cos
  have hw : HasDerivAt (clampedFreeMode L)
      ((Real.pi / (2 * L)) * Real.sin (Real.pi * x / (2 * L))) x := by
    have h := hcos.const_sub (1 : ℝ)
    unfold clampedFreeMode
    convert h using 2
    ring
  exact hw.deriv

/-- Second derivative of the clamped-free mode. -/
lemma iteratedDeriv_two_clampedFreeMode {L : ℝ} (hL : L ≠ 0) (x : ℝ) :
    iteratedDeriv 2 (clampedFreeMode L) x =
      (Real.pi / (2 * L)) ^ 2 * Real.cos (Real.pi * x / (2 * L)) := by
  have hderiv := deriv_clampedFreeMode hL
  have hinner : HasDerivAt (fun x : ℝ => Real.pi * x / (2 * L)) (Real.pi / (2 * L)) x := by
    have hfun : (fun x : ℝ => Real.pi * x / (2 * L)) = fun x => (Real.pi / (2 * L)) * x := by
      funext y
      ring
    rw [hfun]
    exact hasDerivAt_const_mul _
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (Real.pi * x / (2 * L)))
      (Real.cos (Real.pi * x / (2 * L)) * (Real.pi / (2 * L))) x :=
    hinner.sin
  have hsmul : HasDerivAt (fun x : ℝ => (Real.pi / (2 * L)) * Real.sin (Real.pi * x / (2 * L)))
      ((Real.pi / (2 * L)) * (Real.cos (Real.pi * x / (2 * L)) * (Real.pi / (2 * L)))) x :=
    hsin.const_mul _
  have hHas : HasDerivAt (deriv (clampedFreeMode L))
      ((Real.pi / (2 * L)) ^ 2 * Real.cos (Real.pi * x / (2 * L))) x := by
    rw [hderiv]
    convert hsmul using 1
    ring
  have hderiv2 := hHas.deriv
  have hiter : iteratedDeriv 2 (clampedFreeMode L) x = deriv (deriv (clampedFreeMode L)) x := by
    have hsucc : iteratedDeriv (1 + 1) (clampedFreeMode L) = deriv (iteratedDeriv 1 (clampedFreeMode L)) :=
      iteratedDeriv_succ
    rw [iteratedDeriv_one] at hsucc
    have h21 : (2 : ℕ) = 1 + 1 := rfl
    rw [h21]
    exact congrFun hsucc x
  rw [hiter]
  exact hderiv2

/-- Third derivative of the clamped-free mode. -/
lemma iteratedDeriv_three_clampedFreeMode {L : ℝ} (hL : L ≠ 0) (x : ℝ) :
    iteratedDeriv 3 (clampedFreeMode L) x =
      -((Real.pi / (2 * L)) ^ 3) * Real.sin (Real.pi * x / (2 * L)) := by
  have h2fun : iteratedDeriv 2 (clampedFreeMode L) =
      fun x => (Real.pi / (2 * L)) ^ 2 * Real.cos (Real.pi * x / (2 * L)) :=
    funext (fun y => iteratedDeriv_two_clampedFreeMode hL y)
  have hinner : HasDerivAt (fun x : ℝ => Real.pi * x / (2 * L)) (Real.pi / (2 * L)) x := by
    have hfun : (fun x : ℝ => Real.pi * x / (2 * L)) = fun x => (Real.pi / (2 * L)) * x := by
      funext y
      ring
    rw [hfun]
    exact hasDerivAt_const_mul _
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (Real.pi * x / (2 * L)))
      (-Real.sin (Real.pi * x / (2 * L)) * (Real.pi / (2 * L))) x :=
    hinner.cos
  have hsmul : HasDerivAt
      (fun x : ℝ => (Real.pi / (2 * L)) ^ 2 * Real.cos (Real.pi * x / (2 * L)))
      ((Real.pi / (2 * L)) ^ 2 * (-Real.sin (Real.pi * x / (2 * L)) * (Real.pi / (2 * L)))) x :=
    hcos.const_mul _
  have hHas : HasDerivAt (iteratedDeriv 2 (clampedFreeMode L))
      (-((Real.pi / (2 * L)) ^ 3) * Real.sin (Real.pi * x / (2 * L))) x := by
    rw [h2fun]
    convert hsmul using 1
    ring
  have hderiv3 := hHas.deriv
  have hiter : iteratedDeriv 3 (clampedFreeMode L) x =
      deriv (iteratedDeriv 2 (clampedFreeMode L)) x := by
    have hsucc : iteratedDeriv (2 + 1) (clampedFreeMode L) =
        deriv (iteratedDeriv 2 (clampedFreeMode L)) :=
      iteratedDeriv_succ
    have h32 : (3 : ℕ) = 2 + 1 := rfl
    rw [h32]
    exact congrFun hsucc x
  rw [hiter]
  exact hderiv3

/-- Fourth derivative of the clamped-free mode. -/
lemma iteratedDeriv_four_clampedFreeMode {L : ℝ} (hL : L ≠ 0) (x : ℝ) :
    iteratedDeriv 4 (clampedFreeMode L) x =
      -((Real.pi / (2 * L)) ^ 4) * Real.cos (Real.pi * x / (2 * L)) := by
  have h3fun : iteratedDeriv 3 (clampedFreeMode L) =
      fun x => -((Real.pi / (2 * L)) ^ 3) * Real.sin (Real.pi * x / (2 * L)) :=
    funext (fun y => iteratedDeriv_three_clampedFreeMode hL y)
  have hinner : HasDerivAt (fun x : ℝ => Real.pi * x / (2 * L)) (Real.pi / (2 * L)) x := by
    have hfun : (fun x : ℝ => Real.pi * x / (2 * L)) = fun x => (Real.pi / (2 * L)) * x := by
      funext y
      ring
    rw [hfun]
    exact hasDerivAt_const_mul _
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (Real.pi * x / (2 * L)))
      (Real.cos (Real.pi * x / (2 * L)) * (Real.pi / (2 * L))) x :=
    hinner.sin
  have hsmul : HasDerivAt
      (fun x : ℝ => -((Real.pi / (2 * L)) ^ 3) * Real.sin (Real.pi * x / (2 * L)))
      (-((Real.pi / (2 * L)) ^ 3) * (Real.cos (Real.pi * x / (2 * L)) * (Real.pi / (2 * L)))) x :=
    hsin.const_mul _
  have hHas : HasDerivAt (iteratedDeriv 3 (clampedFreeMode L))
      (-((Real.pi / (2 * L)) ^ 4) * Real.cos (Real.pi * x / (2 * L))) x := by
    rw [h3fun]
    convert hsmul using 1
    ring
  have hderiv4 := hHas.deriv
  have hiter : iteratedDeriv 4 (clampedFreeMode L) x =
      deriv (iteratedDeriv 3 (clampedFreeMode L)) x := by
    have hsucc : iteratedDeriv (3 + 1) (clampedFreeMode L) =
        deriv (iteratedDeriv 3 (clampedFreeMode L)) :=
      iteratedDeriv_succ
    have h43 : (4 : ℕ) = 3 + 1 := rfl
    rw [h43]
    exact congrFun hsucc x
  rw [hiter]
  exact hderiv4

/-- Unrestricted algebraic form of the clamped-free column identity,
for every real `EI` (linear in `EI`; the degenerate `EI = 0` case
carries no column mechanics): with axial load `P = π²EI / (4L²)`, the
mode `w = 1 - cos (πx / (2L))` satisfies the fourth-order Euler column
equation `EI * w'''' + P * w'' = 0` at every `x`, the clamped conditions
`w(0) = w'(0) = 0`, and the load-dependent free-end natural conditions
`w''(L) = 0` and `EI * w'''(L) + P * w'(L) = 0`. -/
lemma clampedFree_columnEquation {EI L : ℝ} (hL : 0 < L) :
    (∀ x : ℝ, EI * iteratedDeriv 4 (clampedFreeMode L) x +
        (Real.pi ^ 2 * EI / (4 * L ^ 2)) *
          iteratedDeriv 2 (clampedFreeMode L) x = 0) ∧
      clampedFreeMode L 0 = 0 ∧ deriv (clampedFreeMode L) 0 = 0 ∧
        iteratedDeriv 2 (clampedFreeMode L) L = 0 ∧
          EI * iteratedDeriv 3 (clampedFreeMode L) L +
            (Real.pi ^ 2 * EI / (4 * L ^ 2)) *
              deriv (clampedFreeMode L) L = 0 := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hderiv := deriv_clampedFreeMode hLne
  have hphaseL : Real.pi * L / (2 * L) = Real.pi / 2 := by
    field_simp
  have hc2 : (Real.pi / (2 * L)) ^ 2 = Real.pi ^ 2 / (4 * L ^ 2) := by
    field_simp
    ring
  have hP : Real.pi ^ 2 * EI / (4 * L ^ 2) = EI * (Real.pi / (2 * L)) ^ 2 := by
    rw [hc2]
    ring
  refine ⟨?heq, clampedFreeMode_zero L, ?hderiv0, ?hiter2L, ?hfree⟩
  · intro x
    rw [iteratedDeriv_four_clampedFreeMode hLne x, iteratedDeriv_two_clampedFreeMode hLne x, hP]
    ring
  · rw [hderiv]
    simp
  · rw [iteratedDeriv_two_clampedFreeMode hLne L, hphaseL, Real.cos_pi_div_two, mul_zero]
  · rw [iteratedDeriv_three_clampedFreeMode hLne L, hphaseL, Real.sin_pi_div_two, hderiv]
    dsimp only
    rw [hphaseL, Real.sin_pi_div_two, hP]
    ring

/-- The clamped-free Euler column eigenpair: for positive flexural
rigidity `EI` and column length `L`, `w = 1 - cos (πx / (2L))` at axial
load `P = π²EI / (4L²)` is a buckling eigenfunction of a clamped-free
column. One explicit eigenpair, not a first-eigenvalue or completeness
claim. -/
theorem clampedFree_eigenpair {EI L : ℝ} (hEI : 0 < EI) (hL : 0 < L) :
    (∀ x : ℝ, EI * iteratedDeriv 4 (clampedFreeMode L) x +
        (Real.pi ^ 2 * EI / (4 * L ^ 2)) *
          iteratedDeriv 2 (clampedFreeMode L) x = 0) ∧
      clampedFreeMode L 0 = 0 ∧ deriv (clampedFreeMode L) 0 = 0 ∧
        iteratedDeriv 2 (clampedFreeMode L) L = 0 ∧
          EI * iteratedDeriv 3 (clampedFreeMode L) L +
            (Real.pi ^ 2 * EI / (4 * L ^ 2)) *
              deriv (clampedFreeMode L) L = 0 :=
  clampedFree_columnEquation hL

/-! ## C. The pinned-pinned energy threshold -/

private theorem aux_cos_double {L : ℝ} (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L, Real.cos (2 * (Real.pi * x / L))) = 0 := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have h2pine : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt (by linarith [Real.pi_pos])
  set k : ℝ := 2 * Real.pi / L with hk
  have hkne : k ≠ 0 := by rw [hk]; exact div_ne_zero h2pine hLne
  have harg : ∀ x : ℝ, 2 * (Real.pi * x / L) = k * x := by
    intro x; rw [hk]; field_simp
  simp_rw [harg]
  have hφ : ∀ x : ℝ, HasDerivAt (fun y : ℝ => k * y) k x := fun x => by
    simpa using (hasDerivAt_id x).const_mul k
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (fun y => Real.sin (k * y)) (Real.cos (k * x) * k) x := by
    intro x _
    exact HasDerivAt.sin (hφ x)
  have hlin : ContinuousOn (fun y : ℝ => k * y) (Set.uIcc 0 L) :=
    continuousOn_id.const_mul k
  have hcos : ContinuousOn (fun y => Real.cos (k * y)) (Set.uIcc 0 L) :=
    Real.continuous_cos.comp_continuousOn hlin
  have hcont : ContinuousOn (fun y => Real.cos (k * y) * k) (Set.uIcc 0 L) :=
    hcos.mul_const k
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable
  have hkL : k * L = 2 * Real.pi := by rw [hk]; field_simp
  have hsin2pi : Real.sin (2 * Real.pi) = 0 := by
    simp [Real.sin_two_mul, Real.sin_pi]
  have hbound : Real.sin (k * L) - Real.sin (k * 0) = 0 := by
    rw [hkL, hsin2pi, mul_zero, Real.sin_zero, sub_zero]
  rw [hbound] at hFTC
  have hmul : (∫ y in (0 : ℝ)..L, Real.cos (k * y) * k)
      = (∫ y in (0 : ℝ)..L, Real.cos (k * y)) * k :=
    intervalIntegral.integral_mul_const k _
  have hzero : (∫ y in (0 : ℝ)..L, Real.cos (k * y)) * k = 0 := by
    simp only [← hmul]
    exact hFTC
  exact (mul_eq_zero.mp hzero).resolve_right hkne

private theorem aux_sin_sq {L : ℝ} (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L, (Real.sin (Real.pi * x / L)) ^ 2) = L / 2 := by
  have hcos0 := aux_cos_double hL
  have hid : ∀ x : ℝ, (Real.sin (Real.pi * x / L)) ^ 2
      = 1 / 2 - Real.cos (2 * (Real.pi * x / L)) / 2 := by
    intro x
    have h2 := Real.cos_two_mul (Real.pi * x / L)
    have hsc := Real.sin_sq_add_cos_sq (Real.pi * x / L)
    linear_combination (1 / 2) * h2 + hsc
  have econg : (fun x => (Real.sin (Real.pi * x / L)) ^ 2)
      = (fun x => 1 / 2 - Real.cos (2 * (Real.pi * x / L)) / 2) := funext hid
  rw [econg]
  have hlin : ContinuousOn (fun x : ℝ => Real.pi * x / L) (Set.uIcc 0 L) :=
    (continuousOn_const.mul continuousOn_id).div_const L
  have h2phi : ContinuousOn (fun x : ℝ => 2 * (Real.pi * x / L)) (Set.uIcc 0 L) :=
    hlin.const_mul 2
  have hcosc : ContinuousOn (fun x => Real.cos (2 * (Real.pi * x / L))) (Set.uIcc 0 L) :=
    Real.continuous_cos.comp_continuousOn h2phi
  have hint1 : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) MeasureTheory.volume 0 L :=
    continuousOn_const.intervalIntegrable
  have hint2 : IntervalIntegrable (fun x => Real.cos (2 * (Real.pi * x / L)) / 2)
      MeasureTheory.volume 0 L :=
    (hcosc.div_const 2).intervalIntegrable
  rw [intervalIntegral.integral_sub hint1 hint2]
  have hc1 : (∫ _ in (0 : ℝ)..L, (1 / 2 : ℝ)) = L / 2 := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have hc2 : (∫ x in (0 : ℝ)..L, Real.cos (2 * (Real.pi * x / L)) / 2) = 0 := by
    have hdiv : (∫ x in (0 : ℝ)..L, Real.cos (2 * (Real.pi * x / L)) / 2)
        = (∫ x in (0 : ℝ)..L, Real.cos (2 * (Real.pi * x / L))) / 2 :=
      intervalIntegral.integral_div 2 _
    rw [hdiv, hcos0, zero_div]
  rw [hc1, hc2, sub_zero]

private theorem aux_cos_sq {L : ℝ} (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L, (Real.cos (Real.pi * x / L)) ^ 2) = L / 2 := by
  have hcos0 := aux_cos_double hL
  have hid : ∀ x : ℝ, (Real.cos (Real.pi * x / L)) ^ 2
      = 1 / 2 + Real.cos (2 * (Real.pi * x / L)) / 2 := by
    intro x
    have h2 := Real.cos_two_mul (Real.pi * x / L)
    linear_combination (-1 / 2) * h2
  have econg : (fun x => (Real.cos (Real.pi * x / L)) ^ 2)
      = (fun x => 1 / 2 + Real.cos (2 * (Real.pi * x / L)) / 2) := funext hid
  rw [econg]
  have hlin : ContinuousOn (fun x : ℝ => Real.pi * x / L) (Set.uIcc 0 L) :=
    (continuousOn_const.mul continuousOn_id).div_const L
  have h2phi : ContinuousOn (fun x : ℝ => 2 * (Real.pi * x / L)) (Set.uIcc 0 L) :=
    hlin.const_mul 2
  have hcosc : ContinuousOn (fun x => Real.cos (2 * (Real.pi * x / L))) (Set.uIcc 0 L) :=
    Real.continuous_cos.comp_continuousOn h2phi
  have hint1 : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) MeasureTheory.volume 0 L :=
    continuousOn_const.intervalIntegrable
  have hint2 : IntervalIntegrable (fun x => Real.cos (2 * (Real.pi * x / L)) / 2)
      MeasureTheory.volume 0 L :=
    (hcosc.div_const 2).intervalIntegrable
  rw [intervalIntegral.integral_add hint1 hint2]
  have hc1 : (∫ _ in (0 : ℝ)..L, (1 / 2 : ℝ)) = L / 2 := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have hc2 : (∫ x in (0 : ℝ)..L, Real.cos (2 * (Real.pi * x / L)) / 2) = 0 := by
    have hdiv : (∫ x in (0 : ℝ)..L, Real.cos (2 * (Real.pi * x / L)) / 2)
        = (∫ x in (0 : ℝ)..L, Real.cos (2 * (Real.pi * x / L))) / 2 :=
      intervalIntegral.integral_div 2 _
    rw [hdiv, hcos0, zero_div]
  rw [hc1, hc2, add_zero]

private theorem hasDerivAt_tan_aux {x : ℝ} (h : Real.cos x ≠ 0) :
    HasDerivAt Real.tan (1 / Real.cos x ^ 2) x := by
  have hdiv := (Real.hasDerivAt_sin x).div (Real.hasDerivAt_cos x) h
  have efun : Real.sin / Real.cos = Real.tan :=
    funext fun y => (Real.tan_eq_sin_div_cos y).symm
  have e1 : Real.cos x * Real.cos x - Real.sin x * (-Real.sin x) = 1 := by
    have hsc := Real.sin_sq_add_cos_sq x
    linear_combination hsc
  have ederiv : (Real.cos x * Real.cos x - Real.sin x * (-Real.sin x)) / Real.cos x ^ 2
      = 1 / Real.cos x ^ 2 := by
    rw [e1]
  rwa [efun, ederiv] at hdiv

private theorem wirtinger_pi_aux {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Icc 0 Real.pi, HasDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (Set.Icc 0 Real.pi))
    (h0 : f 0 = 0) (hpi : f Real.pi = 0)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    c ^ 2 * (∫ x in (0 : ℝ)..Real.pi, (f x) ^ 2) ≤
      ∫ x in (0 : ℝ)..Real.pi, (f' x) ^ 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hIcc : Set.uIcc (0 : ℝ) Real.pi = Set.Icc 0 Real.pi := Set.uIcc_of_le hπ.le
  have hf_cont : ContinuousOn f (Set.Icc 0 Real.pi) := HasDerivAt.continuousOn hf
  have hmem : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
      c * (x - Real.pi / 2) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hxπ : x ≤ Real.pi := hx.2
    have hπ2 : (0 : ℝ) < Real.pi / 2 := by linarith
    have h1 : c * (Real.pi / 2) < 1 * (Real.pi / 2) :=
      mul_lt_mul_of_pos_right hc1 hπ2
    rw [one_mul] at h1
    have hlo : -(Real.pi / 2) ≤ x - Real.pi / 2 := by linarith
    have hhi : x - Real.pi / 2 ≤ Real.pi / 2 := by linarith
    have hclo : c * (-(Real.pi / 2)) ≤ c * (x - Real.pi / 2) :=
      mul_le_mul_of_nonneg_left hlo hc0.le
    have hchi : c * (x - Real.pi / 2) ≤ c * (Real.pi / 2) :=
      mul_le_mul_of_nonneg_left hhi hc0.le
    constructor
    · have he : c * (-(Real.pi / 2)) = -(c * (Real.pi / 2)) := by ring
      have hlt : -(Real.pi / 2) < c * (-(Real.pi / 2)) := by
        rw [he]
        linarith [h1]
      linarith [hclo, hlt]
    · linarith [hchi, h1]
  have hcos : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, Real.cos (c * (x - Real.pi / 2)) ≠ 0 :=
    fun x hx => ne_of_gt (Real.cos_pos_of_mem_Ioo (hmem x hx))
  have hφ : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
      HasDerivAt (fun y : ℝ => c * (y - Real.pi / 2)) c x := by
    intro x _
    simpa using HasDerivAt.const_mul c ((hasDerivAt_id x).sub_const (Real.pi / 2))
  have htan : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
      HasDerivAt (fun y => Real.tan (c * (y - Real.pi / 2)))
        ((1 / Real.cos (c * (x - Real.pi / 2)) ^ 2) * c) x := by
    intro x hx
    have ho := hasDerivAt_tan_aux (hcos x hx)
    exact HasDerivAt.comp x ho (hφ x hx)
  have hRic : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
      (-c) * ((1 / Real.cos (c * (x - Real.pi / 2)) ^ 2) * c)
        = -c ^ 2 - (-c * Real.tan (c * (x - Real.pi / 2))) ^ 2 := by
    intro x hx
    have hcosx := hcos x hx
    have htsq : Real.tan (c * (x - Real.pi / 2)) ^ 2
        = Real.sin (c * (x - Real.pi / 2)) ^ 2 / Real.cos (c * (x - Real.pi / 2)) ^ 2 := by
      rw [Real.tan_eq_sin_div_cos, div_pow]
    have hid : (1 : ℝ) + Real.tan (c * (x - Real.pi / 2)) ^ 2
        = 1 / Real.cos (c * (x - Real.pi / 2)) ^ 2 := by
      rw [htsq]
      have hcos2 : Real.cos (c * (x - Real.pi / 2)) ^ 2 ≠ 0 := pow_ne_zero 2 hcosx
      have hsc := Real.sin_sq_add_cos_sq (c * (x - Real.pi / 2))
      rw [eq_div_iff hcos2, add_mul, one_mul, div_mul_cancel₀ _ hcos2]
      linarith [hsc]
    have e1 : (-c) * ((1 / Real.cos (c * (x - Real.pi / 2)) ^ 2) * c)
        = -(c ^ 2) * (1 / Real.cos (c * (x - Real.pi / 2)) ^ 2) := by ring
    rw [e1, ← hid]
    ring
  have hh : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
      HasDerivAt (fun y => -c * Real.tan (c * (y - Real.pi / 2)))
        (-c ^ 2 - (-c * Real.tan (c * (x - Real.pi / 2))) ^ 2) x := by
    intro x hx
    have h1 := HasDerivAt.const_mul (-c) (htan x hx)
    have e := hRic x hx
    rwa [e] at h1
  have hf2 : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
      HasDerivAt (fun y => (f y) ^ 2) (2 * f x * f' x) x := by
    intro x hx
    have hmul := (hf x hx).mul (hf x hx)
    have e1 : (fun y => (f y) ^ 2) = (fun x => f x * f x) := funext fun y => pow_two (f y)
    have ed : f' x * f x + f x * f' x = 2 * f x * f' x := by ring
    rw [e1]
    rwa [ed] at hmul
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt (fun y => (-c * Real.tan (c * (y - Real.pi / 2))) * (f y) ^ 2)
        ((-c ^ 2 - (-c * Real.tan (c * (x - Real.pi / 2))) ^ 2) * (f x) ^ 2
          + (-c * Real.tan (c * (x - Real.pi / 2))) * (2 * f x * f' x)) x := by
    intro x hx
    rw [hIcc] at hx
    exact (hh x hx).mul (hf2 x hx)
  have hh_cont : ContinuousOn (fun y => -c * Real.tan (c * (y - Real.pi / 2)))
      (Set.Icc 0 Real.pi) := HasDerivAt.continuousOn hh
  have hh2cont : ContinuousOn (fun y => (-c * Real.tan (c * (y - Real.pi / 2))) ^ 2)
      (Set.Icc 0 Real.pi) := by
    have h := hh_cont.mul hh_cont
    have e : (fun y => -c * Real.tan (c * (y - Real.pi / 2)))
        * (fun y => -c * Real.tan (c * (y - Real.pi / 2)))
        = (fun y => (-c * Real.tan (c * (y - Real.pi / 2))) ^ 2) :=
      funext fun y => (pow_two _).symm
    rwa [e] at h
  have hf2cont : ContinuousOn (fun y => (f y) ^ 2) (Set.Icc 0 Real.pi) := by
    have h := hf_cont.mul hf_cont
    have e : f * f = (fun y => (f y) ^ 2) := funext fun y => (pow_two _).symm
    rwa [e] at h
  have hf'2cont : ContinuousOn (fun y => (f' y) ^ 2) (Set.Icc 0 Real.pi) := by
    have h := hf'.mul hf'
    have e : f' * f' = (fun y => (f' y) ^ 2) := funext fun y => (pow_two _).symm
    rwa [e] at h
  have hF'cont : ContinuousOn
      (fun y => (-c ^ 2 - (-c * Real.tan (c * (y - Real.pi / 2))) ^ 2) * (f y) ^ 2
        + (-c * Real.tan (c * (y - Real.pi / 2))) * (2 * f y * f' y))
      (Set.Icc 0 Real.pi) := by
    have hA : ContinuousOn
        (fun y => -c ^ 2 - (-c * Real.tan (c * (y - Real.pi / 2))) ^ 2)
        (Set.Icc 0 Real.pi) :=
      continuousOn_const.sub hh2cont
    have h2ff' : ContinuousOn (fun y => 2 * f y * f' y) (Set.Icc 0 Real.pi) :=
      (continuousOn_const.mul hf_cont).mul hf'
    have hB : ContinuousOn
        (fun y => (-c * Real.tan (c * (y - Real.pi / 2))) * (2 * f y * f' y))
        (Set.Icc 0 Real.pi) :=
      hh_cont.mul h2ff'
    exact (hA.mul hf2cont).add hB
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (ContinuousOn.intervalIntegrable (by rw [hIcc]; exact hF'cont))
  have hbound : (-c * Real.tan (c * (Real.pi - Real.pi / 2))) * (f Real.pi) ^ 2
      - (-c * Real.tan (c * (0 - Real.pi / 2))) * (f 0) ^ 2 = 0 := by
    rw [hpi, h0]
    simp
  rw [hbound] at hFTC
  have hexp : ∀ y : ℝ, (f' y) ^ 2
      - ((-c ^ 2 - (-c * Real.tan (c * (y - Real.pi / 2))) ^ 2) * (f y) ^ 2
        + (-c * Real.tan (c * (y - Real.pi / 2))) * (2 * f y * f' y))
      + (-c ^ 2 * (f y) ^ 2)
      = (f' y - (-c * Real.tan (c * (y - Real.pi / 2))) * f y) ^ 2 := by
    intro y
    ring
  have hnonneg : (0 : ℝ) ≤ ∫ y in (0 : ℝ)..Real.pi,
      ((f' y) ^ 2
        - ((-c ^ 2 - (-c * Real.tan (c * (y - Real.pi / 2))) ^ 2) * (f y) ^ 2
          + (-c * Real.tan (c * (y - Real.pi / 2))) * (2 * f y * f' y))
        + (-c ^ 2 * (f y) ^ 2)) :=
    intervalIntegral.integral_nonneg hπ.le (fun u _ => by rw [hexp]; exact sq_nonneg _)
  have hintB : IntervalIntegrable (fun y => (f' y) ^ 2)
      MeasureTheory.volume 0 Real.pi :=
    ContinuousOn.intervalIntegrable (by rw [hIcc]; exact hf'2cont)
  have hintF : IntervalIntegrable
      (fun y => (-c ^ 2 - (-c * Real.tan (c * (y - Real.pi / 2))) ^ 2) * (f y) ^ 2
        + (-c * Real.tan (c * (y - Real.pi / 2))) * (2 * f y * f' y))
      MeasureTheory.volume 0 Real.pi :=
    ContinuousOn.intervalIntegrable (by rw [hIcc]; exact hF'cont)
  have hintC : IntervalIntegrable (fun y => -c ^ 2 * (f y) ^ 2)
      MeasureTheory.volume 0 Real.pi :=
    ContinuousOn.intervalIntegrable (by rw [hIcc]; exact continuousOn_const.mul hf2cont)
  have hintD : IntervalIntegrable (fun y => (f' y) ^ 2
      - ((-c ^ 2 - (-c * Real.tan (c * (y - Real.pi / 2))) ^ 2) * (f y) ^ 2
        + (-c * Real.tan (c * (y - Real.pi / 2))) * (2 * f y * f' y)))
      MeasureTheory.volume 0 Real.pi :=
    ContinuousOn.intervalIntegrable (by rw [hIcc]; exact hf'2cont.sub hF'cont)
  have hsplit1 : (∫ y in (0 : ℝ)..Real.pi, (f' y) ^ 2
      - ((-c ^ 2 - (-c * Real.tan (c * (y - Real.pi / 2))) ^ 2) * (f y) ^ 2
        + (-c * Real.tan (c * (y - Real.pi / 2))) * (2 * f y * f' y)))
      = (∫ y in (0 : ℝ)..Real.pi, (f' y) ^ 2)
        - ∫ y in (0 : ℝ)..Real.pi,
          ((-c ^ 2 - (-c * Real.tan (c * (y - Real.pi / 2))) ^ 2) * (f y) ^ 2
            + (-c * Real.tan (c * (y - Real.pi / 2))) * (2 * f y * f' y)) :=
    intervalIntegral.integral_sub hintB hintF
  have hsplit2 : (∫ y in (0 : ℝ)..Real.pi,
        ((f' y) ^ 2
          - ((-c ^ 2 - (-c * Real.tan (c * (y - Real.pi / 2))) ^ 2) * (f y) ^ 2
            + (-c * Real.tan (c * (y - Real.pi / 2))) * (2 * f y * f' y))
          + (-c ^ 2 * (f y) ^ 2)))
      = (∫ y in (0 : ℝ)..Real.pi, (f' y) ^ 2
          - ((-c ^ 2 - (-c * Real.tan (c * (y - Real.pi / 2))) ^ 2) * (f y) ^ 2
            + (-c * Real.tan (c * (y - Real.pi / 2))) * (2 * f y * f' y)))
        + ∫ y in (0 : ℝ)..Real.pi, (-c ^ 2 * (f y) ^ 2) :=
    intervalIntegral.integral_add hintD hintC
  have hcm : (∫ y in (0 : ℝ)..Real.pi, -c ^ 2 * (f y) ^ 2)
      = -c ^ 2 * ∫ y in (0 : ℝ)..Real.pi, (f y) ^ 2 :=
    intervalIntegral.integral_const_mul _ _
  rw [hsplit2, hsplit1, hcm, hFTC] at hnonneg
  linarith [hnonneg]

/-- Dirichlet Wirtinger inequality on `[0, π]`: for a differentiable
`f` with derivative function `f'` and `f 0 = f π = 0`,
`∫ f^2 ≤ ∫ (f')^2`. -/
theorem wirtinger_pi {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Icc 0 Real.pi, HasDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (Set.Icc 0 Real.pi))
    (h0 : f 0 = 0) (hpi : f Real.pi = 0) :
    (∫ x in (0 : ℝ)..Real.pi, (f x) ^ 2) ≤
      ∫ x in (0 : ℝ)..Real.pi, (f' x) ^ 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hB : (0 : ℝ) ≤ ∫ x in (0 : ℝ)..Real.pi, (f' x) ^ 2 :=
    intervalIntegral.integral_nonneg hπ.le (fun u _ => sq_nonneg _)
  by_contra hcon
  have hlt : (∫ x in (0 : ℝ)..Real.pi, (f' x) ^ 2)
      < ∫ x in (0 : ℝ)..Real.pi, (f x) ^ 2 := not_le.mp hcon
  have hApos : (0 : ℝ) < ∫ x in (0 : ℝ)..Real.pi, (f x) ^ 2 :=
    lt_of_le_of_lt hB hlt
  have hAne : (∫ x in (0 : ℝ)..Real.pi, (f x) ^ 2) ≠ 0 := ne_of_gt hApos
  set A : ℝ := ∫ x in (0 : ℝ)..Real.pi, (f x) ^ 2 with hA
  set B : ℝ := ∫ x in (0 : ℝ)..Real.pi, (f' x) ^ 2 with hBdef
  have h2A : (0 : ℝ) < 2 * A := by linarith [hApos]
  have hAB : (0 : ℝ) < A + B := by linarith [hApos, hB]
  have hc0 : (0 : ℝ) < (A + B) / (2 * A) := div_pos hAB h2A
  have hc1 : (A + B) / (2 * A) < 1 := by
    rw [div_lt_one h2A]
    linarith [hlt]
  have key := wirtinger_pi_aux hf hf' h0 hpi hc0 hc1
  rw [← hA, ← hBdef] at key
  have hAne' : A ≠ 0 := by rw [hA]; exact hAne
  have hsq : ((A + B) / (2 * A)) ^ 2 * A - B = (A - B) ^ 2 / (4 * A) := by
    field_simp
    ring
  have hpos : (0 : ℝ) < (A - B) ^ 2 / (4 * A) := by
    apply div_pos _ (by linarith [hApos])
    apply sq_pos_of_ne_zero
    rw [sub_ne_zero]
    exact ne_of_gt hlt
  linarith [key, hsq, hpos]

/-- Scaled Dirichlet Wirtinger inequality on `[0, L]`: for `L > 0`
and `w 0 = w L = 0`,
`∫ w^2 ≤ (L / π)^2 * ∫ (w')^2`. -/
theorem wirtinger_scaled {L : ℝ} (hL : 0 < L) {w w' : ℝ → ℝ}
    (hw : ∀ x ∈ Set.Icc 0 L, HasDerivAt w (w' x) x)
    (hw' : ContinuousOn w' (Set.Icc 0 L))
    (h0 : w 0 = 0) (hL0 : w L = 0) :
    (∫ x in (0 : ℝ)..L, (w x) ^ 2) ≤
      (L / Real.pi) ^ 2 * ∫ x in (0 : ℝ)..L, (w' x) ^ 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπne : Real.pi ≠ 0 := ne_of_gt hπ
  have hLne : L ≠ 0 := ne_of_gt hL
  have hc : (0 : ℝ) < L / Real.pi := div_pos hL hπ
  have hcne : (L / Real.pi) ≠ 0 := ne_of_gt hc
  have hLπ : (L / Real.pi) * Real.pi = L := by field_simp
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) Real.pi, (L / Real.pi) * t ∈ Set.Icc 0 L := by
    intro t ht
    constructor
    · exact mul_nonneg hc.le ht.1
    · have hle : (L / Real.pi) * t ≤ (L / Real.pi) * Real.pi :=
        mul_le_mul_of_nonneg_left ht.2 hc.le
      rw [hLπ] at hle
      exact hle
  have hφ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (L / Real.pi) * s) (L / Real.pi) t :=
    fun t => by simpa using (hasDerivAt_id t).const_mul (L / Real.pi)
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) Real.pi,
      HasDerivAt (fun s => w ((L / Real.pi) * s))
        (w' ((L / Real.pi) * t) * (L / Real.pi)) t := by
    intro t ht
    exact HasDerivAt.comp t (hw _ (hmem t ht)) (hφ t)
  have hg'cont : ContinuousOn (fun t => w' ((L / Real.pi) * t) * (L / Real.pi))
      (Set.Icc 0 Real.pi) := by
    have hlin : ContinuousOn (fun t : ℝ => (L / Real.pi) * t) (Set.Icc 0 Real.pi) :=
      continuousOn_id.const_mul (L / Real.pi)
    have hcomp : ContinuousOn (fun t => w' ((L / Real.pi) * t)) (Set.Icc 0 Real.pi) :=
      hw'.comp' hlin (fun t ht => hmem t ht)
    exact hcomp.mul_const (L / Real.pi)
  have hg0 : w ((L / Real.pi) * 0) = 0 := by rw [mul_zero]; exact h0
  have hgπ : w ((L / Real.pi) * Real.pi) = 0 := by rw [hLπ]; exact hL0
  have key : (∫ t in (0 : ℝ)..Real.pi, (w ((L / Real.pi) * t)) ^ 2)
      ≤ ∫ t in (0 : ℝ)..Real.pi, (w' ((L / Real.pi) * t) * (L / Real.pi)) ^ 2 :=
    wirtinger_pi hg hg'cont hg0 hgπ
  have hinv : (L / Real.pi)⁻¹ = Real.pi / L := inv_div L Real.pi
  have hsub1 : (∫ t in (0 : ℝ)..Real.pi, (w ((L / Real.pi) * t)) ^ 2)
      = (Real.pi / L) * ∫ y in (0 : ℝ)..L, (w y) ^ 2 := by
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := Real.pi)
      (fun y : ℝ => (w y) ^ 2) hcne
    simpa [hLπ, hinv, smul_eq_mul] using h
  have hsub2 : (∫ t in (0 : ℝ)..Real.pi, (w' ((L / Real.pi) * t) * (L / Real.pi)) ^ 2)
      = (L / Real.pi) * ∫ y in (0 : ℝ)..L, (w' y) ^ 2 := by
    have e : (fun t => (w' ((L / Real.pi) * t) * (L / Real.pi)) ^ 2)
        = (fun t => (L / Real.pi) ^ 2 * (w' ((L / Real.pi) * t)) ^ 2) :=
      funext fun t => by ring
    rw [e]
    have hcm : (∫ t in (0 : ℝ)..Real.pi, (L / Real.pi) ^ 2 * (w' ((L / Real.pi) * t)) ^ 2)
        = (L / Real.pi) ^ 2 * ∫ t in (0 : ℝ)..Real.pi, (w' ((L / Real.pi) * t)) ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    rw [hcm]
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := Real.pi)
      (fun y : ℝ => (w' y) ^ 2) hcne
    have hsub : (∫ t in (0 : ℝ)..Real.pi, (w' ((L / Real.pi) * t)) ^ 2)
        = (Real.pi / L) * ∫ y in (0 : ℝ)..L, (w' y) ^ 2 := by
      simpa [hLπ, hinv, smul_eq_mul] using h
    rw [hsub]
    field_simp
  rw [hsub1, hsub2] at key
  have hmul := mul_le_mul_of_nonneg_left key hc.le
  have e1 : (L / Real.pi) * ((Real.pi / L) * ∫ y in (0 : ℝ)..L, (w y) ^ 2)
      = ∫ y in (0 : ℝ)..L, (w y) ^ 2 := by
    field_simp
  have e2 : (L / Real.pi) * ((L / Real.pi) * ∫ y in (0 : ℝ)..L, (w' y) ^ 2)
      = (L / Real.pi) ^ 2 * ∫ y in (0 : ℝ)..L, (w' y) ^ 2 := by ring
  rw [e1, e2] at hmul
  exact hmul

/-- Integration by parts for a `C^2` deflection vanishing at both
ends: `∫ (w')^2 = -∫ w * w''` on `[0, L]`. -/
theorem integral_deriv_sq_eq_neg {L : ℝ} (hL : 0 < L) {w w' w'' : ℝ → ℝ}
    (hw : ∀ x ∈ Set.Icc 0 L, HasDerivAt w (w' x) x)
    (hw' : ∀ x ∈ Set.Icc 0 L, HasDerivAt w' (w'' x) x)
    (hw'' : ContinuousOn w'' (Set.Icc 0 L))
    (h0 : w 0 = 0) (hL0 : w L = 0) :
    (∫ x in (0 : ℝ)..L, (w' x) ^ 2) =
      -∫ x in (0 : ℝ)..L, w x * w'' x := by
  have hIcc : Set.uIcc (0 : ℝ) L = Set.Icc 0 L := Set.uIcc_of_le hL.le
  have hw_cont : ContinuousOn w (Set.Icc 0 L) := HasDerivAt.continuousOn hw
  have hw'_cont : ContinuousOn w' (Set.Icc 0 L) := HasDerivAt.continuousOn hw'
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (fun y => w y * w' y) (w' x * w' x + w x * w'' x) x := by
    intro x hx
    rw [hIcc] at hx
    exact (hw x hx).mul (hw' x hx)
  have hFcont : ContinuousOn (fun y => w' y * w' y + w y * w'' y) (Set.uIcc 0 L) := by
    rw [hIcc]
    exact (hw'_cont.mul hw'_cont).add (hw_cont.mul hw'')
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hFcont.intervalIntegrable
  simp only [hL0, h0, zero_mul, sub_self] at hFTC
  have hint1 : IntervalIntegrable (fun y => w' y * w' y) MeasureTheory.volume 0 L :=
    ContinuousOn.intervalIntegrable (by rw [hIcc]; exact hw'_cont.mul hw'_cont)
  have hint2 : IntervalIntegrable (fun y => w y * w'' y) MeasureTheory.volume 0 L :=
    ContinuousOn.intervalIntegrable (by rw [hIcc]; exact hw_cont.mul hw'')
  have hsplit : (∫ y in (0 : ℝ)..L, w' y * w' y + w y * w'' y)
      = (∫ y in (0 : ℝ)..L, w' y * w' y) + ∫ y in (0 : ℝ)..L, w y * w'' y :=
    intervalIntegral.integral_add hint1 hint2
  rw [hsplit] at hFTC
  have econg : (fun y => w' y * w' y) = (fun y => (w' y) ^ 2) :=
    funext fun y => (pow_two _).symm
  rw [econg] at hFTC
  linarith [hFTC]

/-- The pinned-column energy threshold: for `L > 0` and a `C^2`
deflection vanishing at both ends,
`∫ (w')^2 ≤ (L / π)^2 * ∫ (w'')^2`. -/
theorem integral_deriv_sq_le {L : ℝ} (hL : 0 < L)
    {w w' w'' : ℝ → ℝ}
    (hw : ∀ x ∈ Set.Icc 0 L, HasDerivAt w (w' x) x)
    (hw' : ∀ x ∈ Set.Icc 0 L, HasDerivAt w' (w'' x) x)
    (hw'' : ContinuousOn w'' (Set.Icc 0 L))
    (h0 : w 0 = 0) (hL0 : w L = 0) :
    (∫ x in (0 : ℝ)..L, (w' x) ^ 2) ≤
      (L / Real.pi) ^ 2 * ∫ x in (0 : ℝ)..L, (w'' x) ^ 2 := by
  have hIcc : Set.uIcc (0 : ℝ) L = Set.Icc 0 L := Set.uIcc_of_le hL.le
  have hw_cont : ContinuousOn w (Set.Icc 0 L) := HasDerivAt.continuousOn hw
  have hw'_cont : ContinuousOn w' (Set.Icc 0 L) := HasDerivAt.continuousOn hw'
  have hw2cont : ContinuousOn (fun x => (w x) ^ 2) (Set.Icc 0 L) := by
    have h := hw_cont.mul hw_cont
    have e : w * w = (fun x => (w x) ^ 2) := funext fun x => (pow_two _).symm
    rwa [e] at h
  have hw''2cont : ContinuousOn (fun x => (w'' x) ^ 2) (Set.Icc 0 L) := by
    have h := hw''.mul hw''
    have e : w'' * w'' = (fun x => (w'' x) ^ 2) := funext fun x => (pow_two _).symm
    rwa [e] at h
  have hwwcont : ContinuousOn (fun x => w x * w'' x) (Set.Icc 0 L) :=
    hw_cont.mul hw''
  set A : ℝ := ∫ x in (0 : ℝ)..L, (w' x) ^ 2 with hA
  set Bw : ℝ := ∫ x in (0 : ℝ)..L, (w x) ^ 2 with hBw
  set Cw : ℝ := ∫ x in (0 : ℝ)..L, (w'' x) ^ 2 with hCw
  set Dw : ℝ := ∫ x in (0 : ℝ)..L, w x * w'' x with hDw
  have hAnon : (0 : ℝ) ≤ A := by
    rw [hA]; exact intervalIntegral.integral_nonneg hL.le (fun u _ => sq_nonneg _)
  have hBnon : (0 : ℝ) ≤ Bw := by
    rw [hBw]; exact intervalIntegral.integral_nonneg hL.le (fun u _ => sq_nonneg _)
  have hCnon : (0 : ℝ) ≤ Cw := by
    rw [hCw]; exact intervalIntegral.integral_nonneg hL.le (fun u _ => sq_nonneg _)
  have hIBP : A = -Dw := by
    rw [hA, hDw]
    exact integral_deriv_sq_eq_neg hL hw hw' hw'' h0 hL0
  have hW : Bw ≤ (L / Real.pi) ^ 2 * A := by
    rw [hBw, hA]
    exact wirtinger_scaled hL hw hw'_cont h0 hL0
  have hCS : Dw ^ 2 ≤ Bw * Cw := by
    have hquad : ∀ t : ℝ, (0 : ℝ) ≤ Bw + 2 * Dw * t + Cw * t ^ 2 := by
      intro t
      have hcont_t : ContinuousOn (fun x => (w x + t * w'' x) ^ 2) (Set.Icc 0 L) := by
        have h1 : ContinuousOn (fun x => w x + t * w'' x) (Set.Icc 0 L) :=
          hw_cont.add (hw''.const_mul t)
        have h2 := h1.mul h1
        have e : (fun x => w x + t * w'' x) * (fun x => w x + t * w'' x)
            = (fun x => (w x + t * w'' x) ^ 2) :=
          funext fun x => (pow_two _).symm
        rwa [e] at h2
      have hnn : (0 : ℝ) ≤ ∫ x in (0 : ℝ)..L, (w x + t * w'' x) ^ 2 :=
        intervalIntegral.integral_nonneg hL.le (fun u _ => sq_nonneg _)
      have econg : (fun x => (w x + t * w'' x) ^ 2)
          = (fun x => (w x) ^ 2 + ((2 * t) * (w x * w'' x) + (t ^ 2) * (w'' x) ^ 2)) :=
        funext fun x => by ring
      rw [econg] at hnn
      have hint1 : IntervalIntegrable (fun x => (w x) ^ 2) MeasureTheory.volume 0 L :=
        ContinuousOn.intervalIntegrable (by rw [hIcc]; exact hw2cont)
      have hint2 : IntervalIntegrable (fun x => (2 * t) * (w x * w'' x))
          MeasureTheory.volume 0 L :=
        ContinuousOn.intervalIntegrable (by rw [hIcc]; exact hwwcont.const_mul (2 * t))
      have hint3 : IntervalIntegrable (fun x => (t ^ 2) * (w'' x) ^ 2)
          MeasureTheory.volume 0 L :=
        ContinuousOn.intervalIntegrable (by rw [hIcc]; exact hw''2cont.const_mul (t ^ 2))
      have hmidcont : ContinuousOn
          (fun x => (2 * t) * (w x * w'' x) + (t ^ 2) * (w'' x) ^ 2)
          (Set.Icc 0 L) :=
        (hwwcont.const_mul (2 * t)).add (hw''2cont.const_mul (t ^ 2))
      have hmid : IntervalIntegrable
          (fun x => (2 * t) * (w x * w'' x) + (t ^ 2) * (w'' x) ^ 2)
          MeasureTheory.volume 0 L :=
        ContinuousOn.intervalIntegrable (by rw [hIcc]; exact hmidcont)
      have ha : (∫ x in (0 : ℝ)..L, (w x) ^ 2 + ((2 * t) * (w x * w'' x)
          + (t ^ 2) * (w'' x) ^ 2))
          = (∫ x in (0 : ℝ)..L, (w x) ^ 2)
            + ∫ x in (0 : ℝ)..L, ((2 * t) * (w x * w'' x) + (t ^ 2) * (w'' x) ^ 2) :=
        intervalIntegral.integral_add hint1 hmid
      have hb : (∫ x in (0 : ℝ)..L, ((2 * t) * (w x * w'' x) + (t ^ 2) * (w'' x) ^ 2))
          = (∫ x in (0 : ℝ)..L, (2 * t) * (w x * w'' x))
            + ∫ x in (0 : ℝ)..L, (t ^ 2) * (w'' x) ^ 2 :=
        intervalIntegral.integral_add hint2 hint3
      have hc2 : (∫ x in (0 : ℝ)..L, (2 * t) * (w x * w'' x))
          = (2 * t) * ∫ x in (0 : ℝ)..L, w x * w'' x :=
        intervalIntegral.integral_const_mul _ _
      have hc3 : (∫ x in (0 : ℝ)..L, (t ^ 2) * (w'' x) ^ 2)
          = (t ^ 2) * ∫ x in (0 : ℝ)..L, (w'' x) ^ 2 :=
        intervalIntegral.integral_const_mul _ _
      rw [ha, hb, hc2, hc3, ← hBw, ← hCw, ← hDw] at hnn
      linear_combination hnn
    by_cases hC0 : Cw = 0
    · have hDw0 : Dw = 0 := by
        by_contra hne
        have h2D : (2 : ℝ) * Dw ≠ 0 := mul_ne_zero (by norm_num) hne
        have hD : Dw ≠ 0 := fun hz => h2D (by simp [hz])
        set t0 : ℝ := -(Bw + 1) / (2 * Dw) with ht0
        have hq := hquad t0
        rw [hC0] at hq
        have ht0v : 2 * Dw * t0 = -(Bw + 1) := by
          rw [ht0]
          field_simp
        rw [ht0v] at hq
        simp only [zero_mul, add_zero] at hq
        linarith [hq]
      rw [hDw0, hC0]
      simp
    · have hCpos : (0 : ℝ) < Cw := lt_of_le_of_ne hCnon (Ne.symm hC0)
      set t0 : ℝ := -Dw / Cw with ht0
      have hq := hquad t0
      have hmul := mul_nonneg hq hCpos.le
      have ealg : (Bw + 2 * Dw * t0 + Cw * t0 ^ 2) * Cw = Bw * Cw - Dw ^ 2 := by
        rw [ht0]
        have hCne : Cw ≠ 0 := hC0
        field_simp
        ring
      rw [ealg] at hmul
      linarith [hmul]
  have hA2 : A ^ 2 ≤ A * ((L / Real.pi) ^ 2 * Cw) := by
    have e1 : A ^ 2 = Dw ^ 2 := by rw [hIBP]; ring
    have e2 : Dw ^ 2 ≤ ((L / Real.pi) ^ 2 * A) * Cw := by
      have hBC := mul_le_mul_of_nonneg_right hW hCnon
      linarith [hCS, hBC]
    rw [e1]
    linarith [e2]
  by_cases hA0 : A = 0
  · rw [hA0]
    have hpos : (0 : ℝ) ≤ (L / Real.pi) ^ 2 * Cw :=
      mul_nonneg (sq_nonneg _) hCnon
    linarith [hpos]
  · have hApos : (0 : ℝ) < A := lt_of_le_of_ne hAnon (Ne.symm hA0)
    have hA2' : A * A ≤ A * ((L / Real.pi) ^ 2 * Cw) := by
      have : A ^ 2 = A * A := by ring
      rw [this] at hA2
      exact hA2
    exact le_of_mul_le_mul_left hA2' hApos

/-- Lower bound for the pinned-column quadratic energy
`Q = EI * ∫ (w'')^2 - P * ∫ (w')^2`: it is at least
`(π^2 * EI / L^2 - P) * ∫ (w')^2`. -/
theorem quadratic_energy_lower {EI L P : ℝ} (hEI : 0 < EI)
    (hL : 0 < L) {w w' w'' : ℝ → ℝ}
    (hw : ∀ x ∈ Set.Icc 0 L, HasDerivAt w (w' x) x)
    (hw' : ∀ x ∈ Set.Icc 0 L, HasDerivAt w' (w'' x) x)
    (hw'' : ContinuousOn w'' (Set.Icc 0 L))
    (h0 : w 0 = 0) (hL0 : w L = 0) :
    (Real.pi ^ 2 * EI / L ^ 2 - P) *
        ∫ x in (0 : ℝ)..L, (w' x) ^ 2 ≤
      EI * (∫ x in (0 : ℝ)..L, (w'' x) ^ 2) -
        P * ∫ x in (0 : ℝ)..L, (w' x) ^ 2 := by
  have hle := integral_deriv_sq_le hL hw hw' hw'' h0 hL0
  have hπ : 0 < Real.pi := Real.pi_pos
  have hm_nonneg : (0 : ℝ) ≤ Real.pi ^ 2 * EI / L ^ 2 := by
    apply div_nonneg _ (sq_nonneg _)
    apply mul_nonneg _ hEI.le
    exact sq_nonneg _
  have h1 : (Real.pi ^ 2 * EI / L ^ 2) * (∫ x in (0 : ℝ)..L, (w' x) ^ 2)
      ≤ (Real.pi ^ 2 * EI / L ^ 2) * ((L / Real.pi) ^ 2 * ∫ x in (0 : ℝ)..L, (w'' x) ^ 2) :=
    mul_le_mul_of_nonneg_left hle hm_nonneg
  have hLne : L ≠ 0 := ne_of_gt hL
  have hπne : Real.pi ≠ 0 := ne_of_gt hπ
  have h2 : (Real.pi ^ 2 * EI / L ^ 2) * ((L / Real.pi) ^ 2 * ∫ x in (0 : ℝ)..L, (w'' x) ^ 2)
      = EI * ∫ x in (0 : ℝ)..L, (w'' x) ^ 2 := by
    field_simp
  rw [h2] at h1
  linarith [h1]

/-- If the deflection is nonzero somewhere on `[0, L]`, the slope
energy `∫ (w')^2` is strictly positive. -/
theorem integral_deriv_sq_pos {L : ℝ} (hL : 0 < L)
    {w w' : ℝ → ℝ}
    (hw : ∀ x ∈ Set.Icc 0 L, HasDerivAt w (w' x) x)
    (hw' : ContinuousOn w' (Set.Icc 0 L))
    (h0 : w 0 = 0)
    (hne : ∃ x : ℝ, x ∈ Set.Icc 0 L ∧ w x ≠ 0) :
    0 < ∫ x in (0 : ℝ)..L, (w' x) ^ 2 := by
  have hIcc : Set.uIcc (0 : ℝ) L = Set.Icc 0 L := Set.uIcc_of_le hL.le
  have hw'2cont : ContinuousOn (fun x => (w' x) ^ 2) (Set.Icc 0 L) := by
    have h := hw'.mul hw'
    have e : w' * w' = (fun x => (w' x) ^ 2) := funext fun x => (pow_two _).symm
    rwa [e] at h
  have hint : IntervalIntegrable (fun x => (w' x) ^ 2) MeasureTheory.volume 0 L :=
    ContinuousOn.intervalIntegrable (by rw [hIcc]; exact hw'2cont)
  have hnonneg : 0 ≤ ∫ x in (0 : ℝ)..L, (w' x) ^ 2 :=
    intervalIntegral.integral_nonneg hL.le (fun u _ => sq_nonneg _)
  by_contra hcon
  have hle : (∫ x in (0 : ℝ)..L, (w' x) ^ 2) ≤ 0 := not_lt.mp hcon
  have hzero : (∫ x in (0 : ℝ)..L, (w' x) ^ 2) = 0 := le_antisymm hle hnonneg
  have hf_ae : (0 : ℝ → ℝ) ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 L)]
      (fun x => (w' x) ^ 2) :=
    Filter.Eventually.of_forall (fun x => sq_nonneg _)
  have hae0 : (fun x => (w' x) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 L)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hL.le hf_ae hint).mp hzero
  have haeW : ∀ᵐ y ∂MeasureTheory.volume, y ∈ Set.Ioc 0 L → w' y = 0 := by
    have h := MeasureTheory.ae_imp_of_ae_restrict hae0
    filter_upwards [h] with y hy
    intro hmem
    have hy2 : (w' y) ^ 2 = 0 := hy hmem
    exact sq_eq_zero_iff.mp hy2
  have hwall : ∀ x ∈ Set.Icc (0 : ℝ) L, w x = 0 := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hxL : x ≤ L := hx.2
    have hsub : Set.uIcc (0 : ℝ) x ⊆ Set.Icc 0 L := by
      rw [Set.uIcc_of_le hx0]
      exact Set.Icc_subset_Icc le_rfl hxL
    have hderx : ∀ y ∈ Set.uIcc (0 : ℝ) x, HasDerivAt w (w' y) y :=
      fun y hy => hw y (hsub hy)
    have hintx : IntervalIntegrable w' MeasureTheory.volume 0 x :=
      ContinuousOn.intervalIntegrable (hw'.mono hsub)
    have hFTCx := intervalIntegral.integral_eq_sub_of_hasDerivAt hderx hintx
    have h0x : (∫ y in (0 : ℝ)..x, w' y) = 0 := by
      apply intervalIntegral.integral_zero_ae
      rw [Set.uIoc_of_le hx0]
      filter_upwards [haeW] with y hy
      intro hmem
      apply hy
      exact ⟨hmem.1, le_trans hmem.2 hxL⟩
    rw [h0x] at hFTCx
    rw [h0] at hFTCx
    linarith [hFTCx]
  obtain ⟨x, hxmem, hxne⟩ := hne
  exact hxne (hwall x hxmem)

/-- Below the critical load `π^2 * EI / L^2`, the quadratic energy
of a deflection that is nonzero somewhere on `[0, L]` is strictly
positive. -/
theorem quadratic_energy_pos_of_lt {EI L P : ℝ} (hEI : 0 < EI)
    (hL : 0 < L) (hP : P < Real.pi ^ 2 * EI / L ^ 2)
    {w w' w'' : ℝ → ℝ}
    (hw : ∀ x ∈ Set.Icc 0 L, HasDerivAt w (w' x) x)
    (hw' : ∀ x ∈ Set.Icc 0 L, HasDerivAt w' (w'' x) x)
    (hw'' : ContinuousOn w'' (Set.Icc 0 L))
    (h0 : w 0 = 0) (hL0 : w L = 0)
    (hne : ∃ x : ℝ, x ∈ Set.Icc 0 L ∧ w x ≠ 0) :
    0 < EI * (∫ x in (0 : ℝ)..L, (w'' x) ^ 2) -
        P * ∫ x in (0 : ℝ)..L, (w' x) ^ 2 := by
  have hw'_cont : ContinuousOn w' (Set.Icc 0 L) := HasDerivAt.continuousOn hw'
  have hApos : (0 : ℝ) < ∫ x in (0 : ℝ)..L, (w' x) ^ 2 :=
    integral_deriv_sq_pos hL hw hw'_cont h0 hne
  have hlow : (Real.pi ^ 2 * EI / L ^ 2 - P) * ∫ x in (0 : ℝ)..L, (w' x) ^ 2
      ≤ EI * (∫ x in (0 : ℝ)..L, (w'' x) ^ 2) - P * ∫ x in (0 : ℝ)..L, (w' x) ^ 2 :=
    quadratic_energy_lower (P := P) hEI hL hw hw' hw'' h0 hL0
  have hmP : (0 : ℝ) < Real.pi ^ 2 * EI / L ^ 2 - P := sub_pos.mpr hP
  have hpos : (0 : ℝ) < (Real.pi ^ 2 * EI / L ^ 2 - P) * ∫ x in (0 : ℝ)..L, (w' x) ^ 2 :=
    mul_pos hmP hApos
  exact lt_of_lt_of_le hpos hlow

/-- The first pinned mode `x ↦ sin (π * x / L)`. -/
noncomputable def pinnedMode (L x : ℝ) : ℝ := Real.sin (Real.pi * x / L)

/-- Integral of the squared pinned mode over `[0, L]` is `L / 2`. -/
theorem integral_pinnedMode_sq {L : ℝ} (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L, (pinnedMode L x) ^ 2) = L / 2 := by
  simp only [pinnedMode]
  exact aux_sin_sq hL

/-- Integral of the squared pinned-mode slope
`(π / L) * cos (π * x / L)` over `[0, L]` is `(π / L)^2 * (L / 2)`. -/
theorem integral_pinnedMode_slope_sq {L : ℝ} (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L,
      ((Real.pi / L) * Real.cos (Real.pi * x / L)) ^ 2) =
      (Real.pi / L) ^ 2 * (L / 2) := by
  have e : (fun x => ((Real.pi / L) * Real.cos (Real.pi * x / L)) ^ 2)
      = (fun x => (Real.pi / L) ^ 2 * (Real.cos (Real.pi * x / L)) ^ 2) :=
    funext fun x => by ring
  rw [e]
  have hcm : (∫ x in (0 : ℝ)..L, (Real.pi / L) ^ 2 * (Real.cos (Real.pi * x / L)) ^ 2)
      = (Real.pi / L) ^ 2 * ∫ x in (0 : ℝ)..L, (Real.cos (Real.pi * x / L)) ^ 2 :=
    intervalIntegral.integral_const_mul _ _
  rw [hcm, aux_cos_sq hL]

/-- Integral of the squared pinned-mode curvature
`-(π / L)^2 * sin (π * x / L)` over `[0, L]` is
`(π / L)^4 * (L / 2)`. -/
theorem integral_pinnedMode_curvature_sq {L : ℝ} (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L,
      (-(Real.pi / L) ^ 2 * Real.sin (Real.pi * x / L)) ^ 2) =
      (Real.pi / L) ^ 4 * (L / 2) := by
  have e : (fun x => (-(Real.pi / L) ^ 2 * Real.sin (Real.pi * x / L)) ^ 2)
      = (fun x => (Real.pi / L) ^ 4 * (Real.sin (Real.pi * x / L)) ^ 2) :=
    funext fun x => by ring
  rw [e]
  have hcm : (∫ x in (0 : ℝ)..L, (Real.pi / L) ^ 4 * (Real.sin (Real.pi * x / L)) ^ 2)
      = (Real.pi / L) ^ 4 * ∫ x in (0 : ℝ)..L, (Real.sin (Real.pi * x / L)) ^ 2 :=
    intervalIntegral.integral_const_mul _ _
  rw [hcm, aux_sin_sq hL]

/-- At the critical load `P = π^2 * EI / L^2`, the quadratic energy
of the pinned sine mode is exactly zero. -/
theorem pinnedMode_energy_eq_zero {EI L : ℝ} (hEI : 0 < EI)
    (hL : 0 < L) :
    EI * (∫ x in (0 : ℝ)..L,
      (-(Real.pi / L) ^ 2 * Real.sin (Real.pi * x / L)) ^ 2) -
      (Real.pi ^ 2 * EI / L ^ 2) * (∫ x in (0 : ℝ)..L,
        ((Real.pi / L) * Real.cos (Real.pi * x / L)) ^ 2) = 0 := by
  have _pos := hEI
  rw [integral_pinnedMode_curvature_sq hL, integral_pinnedMode_slope_sq hL]
  have hLne : L ≠ 0 := ne_of_gt hL
  field_simp
  ring

/-- Above the critical load, the quadratic energy of the pinned
sine mode is strictly negative. -/
theorem pinnedMode_energy_neg {EI L P : ℝ} (hEI : 0 < EI)
    (hL : 0 < L) (hP : Real.pi ^ 2 * EI / L ^ 2 < P) :
    EI * (∫ x in (0 : ℝ)..L,
      (-(Real.pi / L) ^ 2 * Real.sin (Real.pi * x / L)) ^ 2) -
      P * (∫ x in (0 : ℝ)..L,
        ((Real.pi / L) * Real.cos (Real.pi * x / L)) ^ 2) < 0 := by
  have _pos := hEI
  rw [integral_pinnedMode_curvature_sq hL, integral_pinnedMode_slope_sq hL]
  have hLne : L ≠ 0 := ne_of_gt hL
  have hL2 : (0 : ℝ) < L / 2 := by linarith
  have hpiL : (Real.pi / L) ≠ 0 := div_ne_zero Real.pi_ne_zero hLne
  have hspos : (0 : ℝ) < (Real.pi / L) ^ 2 * (L / 2) :=
    mul_pos (sq_pos_of_ne_zero hpiL) hL2
  have heq : EI * ((Real.pi / L) ^ 4 * (L / 2)) - P * ((Real.pi / L) ^ 2 * (L / 2))
      = ((Real.pi / L) ^ 2 * (L / 2)) * ((Real.pi ^ 2 * EI / L ^ 2) - P) := by
    field_simp
  rw [heq]
  exact mul_neg_of_pos_of_neg hspos (sub_neg.mpr hP)

end Elasticity
