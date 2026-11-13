/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.PDE.DiffusiveEnergy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Tests for the diffusive energy estimate

Closed checks, with every hypothesis of `energy_deriv` discharged:

- a constant-in-space profile has zero energy derivative, for every `D ≥ 0` and `U`;
- positive diffusion: the decaying mode `c t x = exp (-t) * sin x` solves `c_t = c_xx`
  (`D = 1`, `U = 0`) on `[0, 2π]`, and its energy derivative is
  `-∫_0^{2π} (exp (-t) * cos x) ^ 2 = -π * exp (-t) ^ 2 < 0`.

Also: `D = 0` conserves energy for every periodic profile, and `dissipation_nonpos` is checked
at `D = 0` and at the decaying mode.
-/

@[expose] public section

open MeasureTheory intervalIntegral Real

namespace MathlibExt.Analysis.PDE.DiffusiveEnergy

/-- `D = 0`: the energy derivative is `0` for every periodic profile. -/
example {L : ℝ} (hL : 0 < L) (c ct cx cxx : ℝ → ℝ → ℝ) (t : ℝ)
    (hct : ∀ t x, HasDerivAt (fun s => c s x) (ct t x) t)
    (hcx : ∀ t x, HasDerivAt (fun y => c t y) (cx t x) x)
    (hcxx : ∀ t x, HasDerivAt (fun y => cx t y) (cxx t x) x)
    (hPDE : ∀ t x, ct t x + (0 : ℝ) * cx t x = 0 * cxx t x)
    (hper_c : ∀ t, c t 0 = c t L) (hper_cx : ∀ t, cx t 0 = cx t L)
    (hInter : HasDerivAt (fun t => ∫ x in (0 : ℝ)..L, (c t x) ^ 2 / 2)
      (∫ x in (0 : ℝ)..L, c t x * ct t x) t)
    (hInt_cxx : IntervalIntegrable (fun x => c t x * cxx t x) volume 0 L)
    (hInt_cx2 : IntervalIntegrable (fun x => (cx t x) ^ 2) volume 0 L)
    (hInt_ccx : IntervalIntegrable (fun x => c t x * cx t x) volume 0 L) :
    HasDerivAt (fun t => ∫ x in (0 : ℝ)..L, (c t x) ^ 2 / 2) 0 t := by
  have h := energy_deriv (L := L) (D := 0) (U := 0) hL (by norm_num) c ct cx cxx t
    hct hcx hcxx hPDE hper_c hper_cx hInter hInt_cxx hInt_cx2 hInt_ccx
  simpa using h

/-- Constant-in-space profile `c t x = a`, any `D ≥ 0` and `U`: every hypothesis is discharged
by a constant derivative or `simp`, and the energy derivative is `0`. -/
example {L D U a : ℝ} (hL : 0 < L) (hD : 0 ≤ D) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => ∫ _ in (0 : ℝ)..L, a ^ 2 / 2) 0 t := by
  have h := energy_deriv (U := U) hL hD (fun _ _ => a) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) t (fun _ _ => hasDerivAt_const _ _) (fun _ _ => hasDerivAt_const _ _)
    (fun _ _ => hasDerivAt_const _ _) (fun _ _ => by simp) (fun _ => rfl) (fun _ => rfl)
    (by simp only [mul_zero, intervalIntegral.integral_zero]; exact hasDerivAt_const _ _)
    (by simp) (by simp) (by simp)
  simpa using h

/-- Positive diffusion: the decaying mode `c t x = exp (-t) * sin x` solves `c_t = c_xx`
(`D = 1`, `U = 0`), and `c` and `c_x` are `2π`-periodic. `energy_deriv` gives the energy
derivative `-∫_0^{2π} (exp (-t) * cos x) ^ 2 = -π * exp (-t) ^ 2`, which is negative. -/
example (t : ℝ) :
    HasDerivAt (fun t => ∫ x in (0 : ℝ)..2 * π, (exp (-t) * sin x) ^ 2 / 2)
      (-(π * exp (-t) ^ 2)) t ∧ -(π * exp (-t) ^ 2) < 0 := by
  have hexp : ∀ s : ℝ, HasDerivAt (fun s => exp (-s)) (-exp (-s)) s := fun s => by
    simpa using (hasDerivAt_neg' (x := s)).exp
  have hE : ∀ s : ℝ, ∫ x in (0 : ℝ)..2 * π, (exp (-s) * sin x) ^ 2 / 2 = π / 2 * exp (-s) ^ 2 := by
    intro s
    have hx : ∀ x, (exp (-s) * sin x) ^ 2 / 2 = exp (-s) ^ 2 / 2 * sin x ^ 2 := fun x => by ring
    simp_rw [hx, intervalIntegral.integral_const_mul, integral_sin_sq]
    simp only [Real.sin_zero, Real.cos_zero, Real.sin_two_pi, Real.cos_two_pi]
    ring
  have hR : ∫ x in (0 : ℝ)..2 * π, exp (-t) * sin x * -(exp (-t) * sin x) =
      -(π * exp (-t) ^ 2) := by
    have hx : ∀ x, exp (-t) * sin x * -(exp (-t) * sin x) = -exp (-t) ^ 2 * sin x ^ 2 :=
      fun x => by ring
    simp_rw [hx, intervalIntegral.integral_const_mul, integral_sin_sq]
    simp only [Real.sin_zero, Real.cos_zero, Real.sin_two_pi, Real.cos_two_pi]
    ring
  have hInter : HasDerivAt (fun s => ∫ x in (0 : ℝ)..2 * π, (exp (-s) * sin x) ^ 2 / 2)
      (∫ x in (0 : ℝ)..2 * π, exp (-t) * sin x * -(exp (-t) * sin x)) t := by
    rw [funext hE, hR]
    convert ((hexp t).pow 2).const_mul (π / 2) using 1
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have h := energy_deriv (L := 2 * π) (D := 1) (U := 0) (by positivity) zero_le_one
    (fun t x => exp (-t) * sin x) (fun t x => -(exp (-t) * sin x))
    (fun t x => exp (-t) * cos x) (fun t x => -(exp (-t) * sin x)) t
    (fun s x => by simpa using (hexp s).mul_const (sin x))
    (fun s x => (hasDerivAt_sin x).const_mul (exp (-s)))
    (fun s x => by simpa using (hasDerivAt_cos x).const_mul (exp (-s)))
    (fun s x => by simp) (fun s => by simp) (fun s => by simp) hInter
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  refine ⟨?_, neg_lt_zero.mpr (by positivity)⟩
  convert h using 1
  have hx : ∀ x, (exp (-t) * cos x) ^ 2 = exp (-t) ^ 2 * cos x ^ 2 := fun x => by ring
  simp_rw [hx, intervalIntegral.integral_const_mul, integral_cos_sq]
  simp only [Real.sin_zero, Real.cos_zero, Real.sin_two_pi, Real.cos_two_pi]
  ring

/-- Dissipation sign at `D = 0`: `0 * ∫ c_x^2 = 0 ≤ 0` is the boundary case. -/
example {L : ℝ} (hL : 0 < L) (cx : ℝ → ℝ → ℝ) (t : ℝ)
    (hInt_cx2 : IntervalIntegrable (fun x => (cx t x) ^ 2) volume 0 L) :
    -(0 : ℝ) * ∫ x in (0 : ℝ)..L, (cx t x) ^ 2 ≤ 0 :=
  dissipation_nonpos hL (by norm_num) cx t hInt_cx2

/-- Dissipation sign at positive diffusion, for the decaying mode's `c_x = exp (-t) * cos x`. -/
example (t : ℝ) : -(1 : ℝ) * ∫ x in (0 : ℝ)..2 * π, (exp (-t) * cos x) ^ 2 ≤ 0 :=
  dissipation_nonpos (by positivity) zero_le_one (fun t x => exp (-t) * cos x) t
    (Continuous.intervalIntegrable (by fun_prop) _ _)

#print axioms energy_deriv
#print axioms dissipation_nonpos

end MathlibExt.Analysis.PDE.DiffusiveEnergy
