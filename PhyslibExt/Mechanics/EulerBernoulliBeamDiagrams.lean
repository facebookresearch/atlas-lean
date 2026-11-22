/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.EulerBernoulliBeam
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp

/-!
# Shear and moment diagrams of the uniformly loaded beam

## i. Overview

For the simply supported Euler--Bernoulli beam under uniform
load `w` (sagging sign convention, bending moment `M = -EI *
y''`, shear `V = M'`), the bending moment is `(w / 2) * (L * x -
x ^ 2)` and the shear is `(w / 2) * (L - 2 * x)`. End moments
vanish, end shears are opposite, `V' = -w` as a function
identity, and the maximum moment on `[0, L]` is `w * L ^ 2 / 8`
at the midpoint. Moment and shear are built directly on the
canonical deflection `uniformLoadDeflection`.

## ii. Key results

- `Mechanics.EulerBernoulli.uniformBeamMoment_eq`: the moment
  formula.
- `Mechanics.EulerBernoulli.uniformBeamShear_eq`: the shear
  formula.
- `Mechanics.EulerBernoulli.uniformBeamMoment_eq_iteratedDeriv`:
  the moment in the canonical `iteratedDeriv 2` form.
- `Mechanics.EulerBernoulli.uniformBeamShear_deriv`: the
  equilibrium law `V' = -w` as a standalone theorem.
- `Mechanics.EulerBernoulli.uniformBeam_endpoints`: end moments,
  end shears, and `V' = -w` (convenience conjunction; the
  individual endpoint facts are also named separately).
- `Mechanics.EulerBernoulli.uniformBeamMoment_midpoint_max`:
  maximum moment `w * L ^ 2 / 8` at the midpoint.

## iii. Table of contents

- A. Moment and shear formulas

## iv. References

- S. Timoshenko, *Strength of Materials, Part I*, 3rd edition,
  1955 (shear and moment diagrams of a uniformly loaded simply
  supported beam).
-/

@[expose] public section

namespace Mechanics.EulerBernoulli

/-! ## A. Moment and shear formulas -/

/-- Bending moment from the canonical uniform-load deflection,
`M = -EI * y''` (sagging sign convention). -/
noncomputable def uniformBeamMoment (w EI L x : ℝ) : ℝ :=
  -EI * deriv (deriv (uniformLoadDeflection w EI L)) x

/-- The bending moment in the canonical iterated-derivative
form used by the `EulerBernoulliBeam` API:
`M = -EI * iteratedDeriv 2 y`. This is the same function as
`uniformBeamMoment`, whose definition uses nested `deriv`;
the bridge lets clients move between the two encodings. -/
lemma uniformBeamMoment_eq_iteratedDeriv (w EI L x : ℝ) :
    uniformBeamMoment w EI L x
      = -EI * iteratedDeriv 2 (uniformLoadDeflection w EI L) x := by
  have h2 : iteratedDeriv 2 (uniformLoadDeflection w EI L)
      = deriv (deriv (uniformLoadDeflection w EI L)) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one]
  unfold uniformBeamMoment
  rw [h2]

/-- Shear as the derivative of bending moment, `V = M'`. -/
noncomputable def uniformBeamShear (w EI L x : ℝ) : ℝ :=
  deriv (uniformBeamMoment w EI L) x

private lemma hasDerivAt_quartic_aux {L x : ℝ} :
    HasDerivAt (fun x : ℝ => L ^ 3 * x - 2 * L * x ^ 3 + x ^ 4)
      (L ^ 3 - 6 * L * x ^ 2 + 4 * x ^ 3) x := by
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have h3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  have h4 : HasDerivAt (fun x : ℝ => x ^ 4) (4 * x ^ 3) x := by
    simpa using hasDerivAt_pow 4 x
  have hA : HasDerivAt (fun y : ℝ => L ^ 3 * y) (L ^ 3 * 1) x :=
    HasDerivAt.const_mul _ hid
  have hB : HasDerivAt (fun y : ℝ => 2 * L * y ^ 3) (2 * L * (3 * x ^ 2)) x :=
    HasDerivAt.const_mul _ h3
  have h := HasDerivAt.fun_add (HasDerivAt.fun_sub hA hB) h4
  convert h using 2
  ring

private lemma deriv_uniformLoadDeflection_aux {w EI L : ℝ} :
    deriv (uniformLoadDeflection w EI L)
      = fun x => w / (24 * EI) * (L ^ 3 - 6 * L * x ^ 2 + 4 * x ^ 3) := by
  funext x
  have hpoly : HasDerivAt (fun x : ℝ => L ^ 3 * x - 2 * L * x ^ 3 + x ^ 4)
      (L ^ 3 - 6 * L * x ^ 2 + 4 * x ^ 3) x :=
    hasDerivAt_quartic_aux
  have hscaled := HasDerivAt.const_mul (w / (24 * EI)) hpoly
  have hev : uniformLoadDeflection w EI L
      =ᶠ[nhds x] (fun y => w / (24 * EI) * (L ^ 3 * y - 2 * L * y ^ 3 + y ^ 4)) := by
    apply Filter.Eventually.of_forall
    intro y
    unfold uniformLoadDeflection
    ring
  have h := HasDerivAt.congr_of_eventuallyEq hscaled hev
  exact h.deriv

private lemma hasDerivAt_cubic_aux {L x : ℝ} :
    HasDerivAt (fun x : ℝ => L ^ 3 - 6 * L * x ^ 2 + 4 * x ^ 3)
      (-12 * L * x + 12 * x ^ 2) x := by
  have hC : HasDerivAt (fun _ : ℝ => L ^ 3) 0 x := hasDerivAt_const x _
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  have hD : HasDerivAt (fun y : ℝ => 6 * L * y ^ 2) (6 * L * (2 * x)) x :=
    HasDerivAt.const_mul _ h2
  have hE : HasDerivAt (fun y : ℝ => 4 * y ^ 3) (4 * (3 * x ^ 2)) x :=
    HasDerivAt.const_mul _ h3
  have h := HasDerivAt.fun_add (HasDerivAt.fun_sub hC hD) hE
  convert h using 1
  ring

private lemma deriv2_uniformLoadDeflection_aux {w EI L : ℝ} :
    deriv (deriv (uniformLoadDeflection w EI L))
      = fun x => w / (24 * EI) * (-12 * L * x + 12 * x ^ 2) := by
  rw [deriv_uniformLoadDeflection_aux]
  funext x
  have hpoly : HasDerivAt (fun x : ℝ => L ^ 3 - 6 * L * x ^ 2 + 4 * x ^ 3)
      (-12 * L * x + 12 * x ^ 2) x :=
    hasDerivAt_cubic_aux
  have h := HasDerivAt.const_mul (w / (24 * EI)) hpoly
  exact h.deriv

/-- The explicit moment diagram for the uniform-load quartic. -/
theorem uniformBeamMoment_eq {w EI L x : ℝ} (hEI : EI ≠ 0) :
    uniformBeamMoment w EI L x = (w / 2) * (L * x - x ^ 2) := by
  have h2 := congrFun (@deriv2_uniformLoadDeflection_aux w EI L) x
  unfold uniformBeamMoment
  rw [h2]
  field_simp
  ring

private lemma uniformBeamMoment_fun_aux {w EI L : ℝ} (hEI : EI ≠ 0) :
    uniformBeamMoment w EI L = fun x => (w / 2) * (L * x - x ^ 2) := by
  funext x
  exact uniformBeamMoment_eq hEI

/-- The explicit shear diagram for the uniform-load quartic. -/
theorem uniformBeamShear_eq {w EI L x : ℝ} (hEI : EI ≠ 0) :
    uniformBeamShear w EI L x = (w / 2) * (L - 2 * x) := by
  have hfun := @uniformBeamMoment_fun_aux w EI L hEI
  unfold uniformBeamShear
  rw [hfun]
  have hpoly : HasDerivAt (fun x : ℝ => L * x - x ^ 2) (L - 2 * x) x := by
    have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have hA : HasDerivAt (fun y : ℝ => L * y) (L * 1) x :=
      HasDerivAt.const_mul _ hid
    have h := HasDerivAt.fun_sub hA h2
    convert h using 1
    ring
  have h := HasDerivAt.const_mul (w / 2) hpoly
  exact h.deriv

/-- Shear and moment endpoints for the simply supported uniform
load: zero moment at both supports and opposite end shears. -/
theorem uniformBeam_endpoints {w EI L : ℝ} (hEI : EI ≠ 0) :
    uniformBeamMoment w EI L 0 = 0
      ∧ uniformBeamMoment w EI L L = 0
      ∧ uniformBeamShear w EI L 0 = w * L / 2
      ∧ uniformBeamShear w EI L L = -(w * L / 2)
      ∧ deriv (uniformBeamShear w EI L) = fun _ => -w := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [uniformBeamMoment_eq hEI]
    ring
  · rw [uniformBeamMoment_eq hEI]
    ring
  · rw [uniformBeamShear_eq hEI]
    ring
  · rw [uniformBeamShear_eq hEI]
    ring
  · have hsh : uniformBeamShear w EI L = fun x => (w / 2) * (L - 2 * x) := by
      funext x
      exact uniformBeamShear_eq hEI
    rw [hsh]
    funext x
    show deriv (fun x => (w / 2) * (L - 2 * x)) x = -w
    have hlin : HasDerivAt (fun x : ℝ => L - 2 * x) (-2) x := by
      have hC : HasDerivAt (fun _ : ℝ => L) 0 x := hasDerivAt_const x _
      have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
      have hD : HasDerivAt (fun y : ℝ => 2 * y) (2 * 1) x :=
        HasDerivAt.const_mul _ hid
      have h := HasDerivAt.fun_sub hC hD
      convert h using 1
      ring
    have h := HasDerivAt.const_mul (w / 2) hlin
    calc deriv (fun x => (w / 2) * (L - 2 * x)) x
        = (w / 2) * (-2) := h.deriv
      _ = -w := by ring

/-- Zero bending moment at the left support. This endpoint
fact needs no nondegeneracy hypothesis on `EI`: it is the
canonical second-derivative endpoint through the
iterated-derivative bridge. -/
theorem uniformBeamMoment_zero {w EI L : ℝ} :
    uniformBeamMoment w EI L 0 = 0 := by
  rw [uniformBeamMoment_eq_iteratedDeriv,
    uniformLoadDeflection_secondDeriv_zero_left, mul_zero]

/-- Zero bending moment at the right support. As at the left
support, no nondegeneracy hypothesis on `EI` is needed. -/
theorem uniformBeamMoment_at_right {w EI L : ℝ} :
    uniformBeamMoment w EI L L = 0 := by
  rw [uniformBeamMoment_eq_iteratedDeriv,
    uniformLoadDeflection_secondDeriv_zero_right, mul_zero]

/-- Left end shear `w * L / 2`. -/
theorem uniformBeamShear_zero {w EI L : ℝ} (hEI : EI ≠ 0) :
    uniformBeamShear w EI L 0 = w * L / 2 :=
  (uniformBeam_endpoints hEI).2.2.1

/-- Right end shear `-(w * L / 2)`. -/
theorem uniformBeamShear_at_right {w EI L : ℝ} (hEI : EI ≠ 0) :
    uniformBeamShear w EI L L = -(w * L / 2) :=
  (uniformBeam_endpoints hEI).2.2.2.1

/-- Equilibrium law: the shear derivative is the negative
uniform load, `V' = -w`, as a standalone function identity. -/
theorem uniformBeamShear_deriv {w EI L : ℝ} (hEI : EI ≠ 0) :
    deriv (uniformBeamShear w EI L) = fun _ => -w :=
  (uniformBeam_endpoints hEI).2.2.2.2

/-- The maximum bending moment on `[0, L]` is `w * L ^ 2 / 8`,
attained at the midpoint. -/
theorem uniformBeamMoment_midpoint_max {w EI L : ℝ} (hEI : EI ≠ 0)
    (hw : 0 ≤ w) (hL : 0 ≤ L) :
    uniformBeamMoment w EI L (L / 2) = w * L ^ 2 / 8
      ∧ L / 2 ∈ Set.Icc 0 L
      ∧ ∀ x ∈ Set.Icc 0 L,
        uniformBeamMoment w EI L x ≤ w * L ^ 2 / 8 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [uniformBeamMoment_eq hEI]
    ring
  · exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · intro x _
    rw [uniformBeamMoment_eq hEI]
    have hsq : 0 ≤ (x - L / 2) ^ 2 := sq_nonneg _
    have hnonneg : 0 ≤ (w / 2) * (x - L / 2) ^ 2 := mul_nonneg (by linarith) hsq
    have heq : (w / 2) * (L * x - x ^ 2)
        = w * L ^ 2 / 8 - (w / 2) * (x - L / 2) ^ 2 := by ring
    linarith


end Mechanics.EulerBernoulli
