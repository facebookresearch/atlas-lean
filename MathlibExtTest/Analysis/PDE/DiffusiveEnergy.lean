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
- interval-scoped data: a constant profile whose time-derivative field is `0` on `[0, L]` and
  `1` outside, so the PDE holds only on `[0, L]`; the energy derivative is still `0`;
- positive diffusion: the decaying mode `c t x = exp (-t) * sin x` solves `c_t = c_xx`
  (`D = 1`, `U = 0`) on `[0, 2π]`, and its energy derivative is
  `-∫_0^{2π} (exp (-t) * cos x) ^ 2 = -π * exp (-t) ^ 2 < 0`.

Also: `D = 0` conserves energy for every profile that is periodic at `t` and satisfies the
hypotheses indexed by `x ∈ [0, L]` at `t`, and `dissipation_nonpos` is checked at `D = 0` and
at the decaying mode.
-/

@[expose] public section

open MeasureTheory intervalIntegral Real

namespace MathlibExt.Analysis.PDE.DiffusiveEnergy

/-- `D = 0`: the energy derivative is `0` for every profile that is periodic at `t`, with the
derivative and PDE hypotheses indexed by `x ∈ [0, L]` at `t`. -/
example {L : ℝ} (hL : 0 < L) (c ct cx cxx : ℝ → ℝ → ℝ) (t : ℝ)
    (hct : ∀ x ∈ Set.uIcc 0 L, HasDerivAt (fun s => c s x) (ct t x) t)
    (hcx : ∀ x ∈ Set.uIcc 0 L, HasDerivAt (fun y => c t y) (cx t x) x)
    (hcxx : ∀ x ∈ Set.uIcc 0 L, HasDerivAt (fun y => cx t y) (cxx t x) x)
    (hPDE : ∀ x ∈ Set.uIcc 0 L, ct t x + (0 : ℝ) * cx t x = 0 * cxx t x)
    (hper_c : c t 0 = c t L) (hper_cx : cx t 0 = cx t L)
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
    (fun _ _ => hasDerivAt_const _ _) (fun _ _ => by simp) rfl rfl
    (by simp only [mul_zero, intervalIntegral.integral_zero]; exact hasDerivAt_const _ _)
    (by simp) (by simp) (by simp)
  simpa using h

open scoped Classical in
/-- Interval-scoped data: the constant profile `c t x = a` with the time-derivative field
`ct t x = 0` on `[0, L]` and `1` outside. The PDE `ct + U * c_x = D * c_xx` holds on `[0, L]`
and fails outside it; `energy_deriv` needs it only on `[0, L]`, and the energy derivative is
`0`. The profile itself is constant everywhere, so this exercises only the scoping of the PDE.
-/
example {L D U a : ℝ} (hL : 0 < L) (hD : 0 ≤ D) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => ∫ _ in (0 : ℝ)..L, a ^ 2 / 2) 0 t := by
  have hzero : ∫ x in (0 : ℝ)..L, a * (if x ∈ Set.uIcc 0 L then (0 : ℝ) else 1) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => by simp [hx]]
    simp
  have h := energy_deriv (U := U) hL hD (fun _ _ => a)
    (fun _ x => if x ∈ Set.uIcc 0 L then 0 else 1) (fun _ _ => 0) (fun _ _ => 0) t
    (fun x hx => by simpa [hx] using hasDerivAt_const t a) (fun _ _ => hasDerivAt_const _ _)
    (fun _ _ => hasDerivAt_const _ _) (fun x hx => by simp [hx]) rfl rfl
    (by rw [hzero]; exact hasDerivAt_const _ _) (by simp) (by simp) (by simp)
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
    (fun x _ => by simpa using (hexp t).mul_const (sin x))
    (fun x _ => (hasDerivAt_sin x).const_mul (exp (-t)))
    (fun x _ => by simpa using (hasDerivAt_cos x).const_mul (exp (-t)))
    (fun x _ => by simp) (by simp) (by simp) hInter
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
