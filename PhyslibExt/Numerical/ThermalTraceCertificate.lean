/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Logic.Function.Iterate
public import PhyslibExt.Numerical.PhysicalErrorBudgets
import Mathlib.Tactic.Ring

/-!
# Rational thermal trace certificate: checker and soundness

A lumped body cooling in a fixed bath (`PhysicalErrorBudgets`, sections F-H) from the temperature
`T_0 = T_amb + Δ` reaches, after `j` explicit Euler steps of size `τ / 10`, the temperature
`T_j = T_amb + Δ y_j` with the coefficient `y_j = (9 / 10) ^ j`, `j = 0, …, 10`: each step
multiplies the excess `T - T_amb` by `9 / 10`. For `Δ ≠ 0` the coefficient is the normalized excess
`(T_j - T_amb) / Δ`. At `Δ = 0` every `T_j` is `T_amb`, the coefficient form holds for every trace,
and the quotient, Lean's `0 / 0 = 0`, does not recover `y_j`. This file checks a trace of
coefficients as data and binds an accepted trace to the proved analytic bound, for every `Δ`.

## i. Overview

The checker `checkThermalTrace` reads a list of rationals and returns a `Bool`. It accepts exactly
when the list has eleven entries `y_0, …, y_10`, the first is the initial coefficient `y_0 = 1`,
and all ten identities `y_(j+1) = (9 / 10) y_j` hold. The certificate is that
eleven-element list, its last entry `y_10` included and checked by the last identity; there is no
separately supplied expected terminal value or error bound, and floating-point behavior does not
enter. Acceptance is decided by kernel reduction (`decide +kernel`), and how the list was produced
(a file, a parser, a floating-point program) is outside the claim.

Soundness: an accepted list satisfies `y_j = (9 / 10) ^ j` after the cast to the reals, by
induction on the ten identities in `ℚ` and the cast homomorphism; in particular the terminal value
is `(9 / 10) ^ 10`. The physical endpoint `T_amb + Δ y_10` reconstructed from an accepted trace is
the tenth Euler iterate from `T_amb + Δ` (`PhysicalErrorBudgets.bathEuler_closed_form`), so the
proved ten-step bound `PhysicalErrorBudgets.bathEuler_tenStep_error` applies to it:
`|T_amb + Δ y_10 - T(τ)| ≤ |Δ| / 10` for `C, G > 0` and every real `Δ`; at `Δ = 0` the endpoint
and `T(τ)` are both `T_amb`.

Model inputs: those of the bath model (constant `C > 0`, `G > 0`, `T_amb`, the linear bath law).
Non-goals: no floating-point or compiled-code refinement, no parser, no general Euler convergence
theorem, and no empirical adequacy or system safety claim.

## ii. Key results

- `ThermalTraceCertificate.checkThermalTrace`: the eleven-value Boolean checker.
- `ThermalTraceCertificate.checkThermalTrace_sound`,
  `ThermalTraceCertificate.checkThermalTrace_terminal`: acceptance gives `y_j = (9 / 10) ^ j` in
  the reals, and the terminal value.
- `ThermalTraceCertificate.traceEndpoint`,
  `ThermalTraceCertificate.traceEndpoint_eq_iterate`,
  `ThermalTraceCertificate.traceEndpoint_error`: the reconstructed endpoint is the tenth Euler
  iterate and lies within `|Δ| / 10` of `T(τ)`.
- The accepted exact trace, four rejected traces, the endpoint of a body at `350` in a bath at
  `300`, and the same body started at the bath temperature (`Δ = 0`) are in
  `PhyslibExtTest.Numerical.ThermalTraceCertificateTest`.

## iii. Table of contents

- A. The trace checker
- B. Soundness
- C. The physical endpoint and its analytic bound

## iv. References

- E. Hairer, S. P. Nørsett and G. Wanner, *Solving Ordinary Differential Equations I*, 2nd ed.,
  Springer (1993), Section I.7 (the explicit Euler method).
- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine, *Fundamentals of Heat and Mass
  Transfer*, 7th ed., Wiley (2011), Section 5.1 (the lumped capacitance method).
- Y. Bertot and P. Castéran, *Interactive Theorem Proving and Program Development*, Springer
  (2004), Chapter 16 (proof by reflection: a Boolean checker evaluated by the kernel).
- `PhysicalErrorBudgets.bathEuler_closed_form` and `PhysicalErrorBudgets.bathEuler_tenStep_error`.
-/

@[expose] public section

namespace ThermalTraceCertificate

open PhysicalErrorBudgets

/-! ## A. The trace checker -/

/-- **The trace checker.** Accept a list `y` of rationals exactly when it has eleven entries
`y_0, …, y_10`, the first is the initial coefficient `y_0 = 1`, and all ten identities
`y_(j+1) = (9 / 10) y_j`, `j = 0, …, 9`, hold. The entries are the coefficients of
`T_j = T_amb + Δ y_j`, the normalized excesses `(T_j - T_amb) / Δ` only for `Δ ≠ 0`. Entries are
read with the default `0`, which an accepted list never uses. The certificate is the
eleven-element list itself, `y_10` included; there is no separately supplied expected terminal
value or error bound. -/
def checkThermalTrace (y : List ℚ) : Bool :=
  y.length == 11 && y.getD 0 0 == 1 &&
    (List.range 10).all fun j => y.getD (j + 1) 0 == 9 / 10 * y.getD j 0

/-! ## B. Soundness -/

private lemma checkThermalTrace_rat {y : List ℚ} (h : checkThermalTrace y = true) :
    y.length = 11 ∧ ∀ j ≤ 10, y.getD j 0 = (9 / 10 : ℚ) ^ j := by
  unfold checkThermalTrace at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hlen, h0⟩, hstep⟩ := h
  refine ⟨hlen, fun j hj => ?_⟩
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    rw [hstep j (by omega), ih (by omega), pow_succ]
    ring

/-- **Soundness.** An accepted list has eleven entries, and `y_j = (9 / 10) ^ j` for
`j = 0, …, 10` after the cast to the reals. -/
lemma checkThermalTrace_sound {y : List ℚ} (h : checkThermalTrace y = true) :
    y.length = 11 ∧ ∀ j ≤ 10, ((y.getD j 0 : ℚ) : ℝ) = (9 / 10 : ℝ) ^ j := by
  obtain ⟨hlen, hy⟩ := checkThermalTrace_rat h
  refine ⟨hlen, fun j hj => ?_⟩
  rw [hy j hj]
  push_cast
  ring

/-- **Terminal value.** An accepted trace ends at `y_10 = (9 / 10) ^ 10` in the reals. -/
lemma checkThermalTrace_terminal {y : List ℚ} (h : checkThermalTrace y = true) :
    ((y.getD 10 0 : ℚ) : ℝ) = (9 / 10 : ℝ) ^ 10 := by
  exact (checkThermalTrace_sound h).2 10 le_rfl

/-! ## C. The physical endpoint and its analytic bound -/

/-- The physical endpoint `T_amb + Δ y_10` reconstructed from a trace `y` of coefficients,
`T_j = T_amb + Δ y_j`, for the bath temperature `T_amb` and the initial excess `Δ = T_0 - T_amb`.
`Δ` may be `0`; the endpoint is then `T_amb` for every trace. -/
noncomputable def traceEndpoint (Tamb Δ : ℝ) (y : List ℚ) : ℝ :=
  Tamb + Δ * (y.getD 10 0 : ℝ)

private lemma bathEuler_iterate_succ (C G Tamb dt x : ℝ) (j : ℕ) :
    (bathEulerStep C G Tamb dt)^[j + 1] x = bathEulerStep C G Tamb dt
      ((bathEulerStep C G Tamb dt)^[j] x) :=
  Function.iterate_succ_apply' _ _ _

/-- **The certified endpoint is the tenth Euler iterate.** For `C, G > 0` and an accepted trace,
`T_amb + Δ y_10` is the result of ten explicit Euler steps of size `τ / 10`, `τ = C / G`, started
at `T_amb + Δ`. -/
lemma traceEndpoint_eq_iterate {C G : ℝ} (hC : 0 < C) (hG : 0 < G) (Tamb Δ : ℝ) {y : List ℚ}
    (h : checkThermalTrace y = true) :
    traceEndpoint Tamb Δ y =
      (bathEulerStep C G Tamb (thermalTimeConstant C G / 10))^[10] (Tamb + Δ) := by
  have hcf := bathEuler_closed_form hC hG (Tamb := Tamb) (Δ := Δ)
    (X := fun j => (bathEulerStep C G Tamb (thermalTimeConstant C G / 10))^[j] (Tamb + Δ))
    rfl (fun j => bathEuler_iterate_succ C G Tamb _ (Tamb + Δ) j) 10
  rw [traceEndpoint, checkThermalTrace_terminal h]
  exact hcf.symm

/-- **Analytic bound for the certified endpoint.** For `C, G > 0` and an accepted trace, the
reconstructed endpoint lies within `|Δ| / 10` of the exact bath trajectory at `t = τ`. -/
lemma traceEndpoint_error {C G : ℝ} (hC : 0 < C) (hG : 0 < G) (Tamb Δ : ℝ) {y : List ℚ}
    (h : checkThermalTrace y = true) :
    |traceEndpoint Tamb Δ y - bathTrajectory C G Tamb Δ (thermalTimeConstant C G)| ≤ |Δ| / 10 := by
  rw [traceEndpoint_eq_iterate hC hG Tamb Δ h]
  exact bathEuler_tenStep_error hC hG
    (X := fun j => (bathEulerStep C G Tamb (thermalTimeConstant C G / 10))^[j] (Tamb + Δ))
    rfl (fun j => bathEuler_iterate_succ C G Tamb _ (Tamb + Δ) j)

end ThermalTraceCertificate
