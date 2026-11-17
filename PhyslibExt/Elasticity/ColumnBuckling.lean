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

## iii. Table of contents

- A. The clamped-clamped mode
- B. The clamped-free mode

## iv. References

- J. E. Shigley, C. R. Mischke, *Mechanical Engineering Design*
  (McGraw-Hill): columns and the Euler column formula, including
  end-condition-dependent effective lengths; the fixed-fixed (both ends
  clamped) case has theoretical effective-length factor `K = 1/2`, so
  the first fixed-fixed buckling load is `4π²EI / L²`, matching the
  eigenpair verified here. Authorship across editions changes
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

end Elasticity
