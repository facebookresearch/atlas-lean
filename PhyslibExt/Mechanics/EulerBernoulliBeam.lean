/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Uniform-load beam witness

## i. Overview

For a simply supported Euler–Bernoulli beam of length `L` and constant
bending stiffness `EI` under uniform load `w`, the quartic
`y(x) = w * (L^3 * x - 2 * L * x^3 + x^4) / (24 * EI)`, with
downward-positive deflection, is a witness of the beam boundary value
problem: it satisfies `EI * y'''' = w` and the four simple-support
conditions `y(0) = y(L) = y''(0) = y''(L) = 0`. This is one load-case
witness, not a BVP existence theory or a beam library.

## ii. Key results

- `Mechanics.EulerBernoulli.uniformLoadDeflection`: the quartic
  deflection.
- `Mechanics.EulerBernoulli.uniformLoadDeflection_zero_left`,
  `Mechanics.EulerBernoulli.uniformLoadDeflection_zero_right`: support
  deflections vanish.
- `Mechanics.EulerBernoulli.uniformLoadDeflection_secondDeriv_zero_left`,
  `Mechanics.EulerBernoulli.uniformLoadDeflection_secondDeriv_zero_right`:
  end moments vanish.
- `Mechanics.EulerBernoulli.uniformLoadDeflection_ei_mul_iteratedDeriv_four`:
  `EI * y'''' = w`.

## iii. Table of contents

- A. The quartic witness and its boundary conditions

## iv. References

- S. Timoshenko, *Strength of Materials, Part I*, 3rd edition, 1955
  (uniformly loaded simply supported beam).
-/

@[expose] public section

namespace Mechanics.EulerBernoulli

/-! ## A. The quartic witness and its boundary conditions -/

/-- Downward-positive deflection of a simply supported Euler--Bernoulli beam of length `L`, bending
stiffness `EI`, under uniform load `w`: `w * (L^3*x - 2*L*x^3 + x^4) / (24 * EI)`. With the
convention `x / 0 = 0` it is identically `0` when `EI = 0`; physically `EI > 0`. -/
noncomputable def uniformLoadDeflection (w EI L x : ℝ) : ℝ :=
  w * (L ^ 3 * x - 2 * L * x ^ 3 + x ^ 4) / (24 * EI)

private lemma iteratedDeriv_uniformLoadDeflection (w EI L : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (uniformLoadDeflection w EI L) x =
      w * (L ^ 3 * iteratedDeriv n (fun x : ℝ => x) x
        - (2 * L) * iteratedDeriv n (fun x : ℝ => x ^ 3) x
        + iteratedDeriv n (fun x : ℝ => x ^ 4) x) / (24 * EI) := by
  have h1 : ContDiffAt ℝ n (fun x : ℝ => L ^ 3 * x - 2 * L * x ^ 3) x := by fun_prop
  have h2 : ContDiffAt ℝ n (fun x : ℝ => x ^ 4) x := by fun_prop
  have h3 : ContDiffAt ℝ n (fun x : ℝ => L ^ 3 * x) x := by fun_prop
  have h4 : ContDiffAt ℝ n (fun x : ℝ => 2 * L * x ^ 3) x := by fun_prop
  unfold uniformLoadDeflection
  simp only [iteratedDeriv_div_const, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_add h1 h2, iteratedDeriv_fun_sub h3 h4]
  rw [iteratedDeriv_const_mul_field]

/-- The deflection vanishes at the left support. -/
theorem uniformLoadDeflection_zero_left (w EI L : ℝ) :
    uniformLoadDeflection w EI L 0 = 0 := by
  unfold uniformLoadDeflection
  ring

/-- The deflection vanishes at the right support. -/
theorem uniformLoadDeflection_zero_right (w EI L : ℝ) :
    uniformLoadDeflection w EI L L = 0 := by
  unfold uniformLoadDeflection
  ring

/-- The bending moment, proportional to the second derivative, vanishes at
the left simple support. -/
theorem uniformLoadDeflection_secondDeriv_zero_left (w EI L : ℝ) :
    iteratedDeriv 2 (uniformLoadDeflection w EI L) 0 = 0 := by
  have e1 : iteratedDeriv 2 (fun x : ℝ => x) 0 = 0 := by simp [iteratedDeriv_fun_id]
  have e3 : iteratedDeriv 2 (fun x : ℝ => x ^ 3) 0 = 0 := by simp [iteratedDeriv_pow]
  have e4 : iteratedDeriv 2 (fun x : ℝ => x ^ 4) 0 = 0 := by simp [iteratedDeriv_pow]
  rw [iteratedDeriv_uniformLoadDeflection, e1, e3, e4]
  ring

/-- The bending moment vanishes at the right simple support. -/
theorem uniformLoadDeflection_secondDeriv_zero_right (w EI L : ℝ) :
    iteratedDeriv 2 (uniformLoadDeflection w EI L) L = 0 := by
  have e1 : iteratedDeriv 2 (fun x : ℝ => x) L = 0 := by simp [iteratedDeriv_fun_id]
  have e3 : iteratedDeriv 2 (fun x : ℝ => x ^ 3) L = 6 * L := by simp [iteratedDeriv_pow]
  have e4 : iteratedDeriv 2 (fun x : ℝ => x ^ 4) L = 12 * L ^ 2 := by simp [iteratedDeriv_pow]
  rw [iteratedDeriv_uniformLoadDeflection, e1, e3, e4]
  ring

/-- The quartic witness satisfies `EI * y'''' = w` everywhere. -/
theorem uniformLoadDeflection_ei_mul_iteratedDeriv_four (w EI L : ℝ)
    (hEI : 0 < EI) (x : ℝ) :
    EI * iteratedDeriv 4 (uniformLoadDeflection w EI L) x = w := by
  have e1 : iteratedDeriv 4 (fun x : ℝ => x) x = 0 := by simp [iteratedDeriv_fun_id]
  have e3 : iteratedDeriv 4 (fun x : ℝ => x ^ 3) x = 0 := by simp [iteratedDeriv_pow]
  have e4 : iteratedDeriv 4 (fun x : ℝ => x ^ 4) x = 24 := by simp [iteratedDeriv_pow]
  rw [iteratedDeriv_uniformLoadDeflection, e1, e3, e4]
  have hEI' : EI ≠ 0 := ne_of_gt hEI
  field_simp
  ring

end Mechanics.EulerBernoulli
