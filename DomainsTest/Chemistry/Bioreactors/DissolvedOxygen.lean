/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Domains.Chemistry.Bioreactors.DissolvedOxygen
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!

# Tests for the dissolved-oxygen balance

Explicit solutions of `C' = K_L a (C* - C) - u(t) - D(t) C`: aeration of oxygen-free liquid,
the constant equilibrium of constant inputs, the boundary case `u = K_L a C*`, and a solution that
leaves `[0, C*]` once the uptake exceeds `K_L a C*`.

-/

@[expose] public section

open Set Real Chemistry.Bioreactors.DissolvedOxygen

namespace DomainsTest.Chemistry.Bioreactors.DissolvedOxygen

/-- Aeration without uptake or dilution: `C(t) = C* - (C* - C₀) e^{-K_L a t}` solves the balance
with `u = D = 0`. -/
theorem hasDerivWithinAt_aeration (kLa Cstar C₀ T t : ℝ) :
    HasDerivWithinAt (fun s ↦ Cstar - (Cstar - C₀) * exp (-kLa * s))
      (kLa * (Cstar - (Cstar - (Cstar - C₀) * exp (-kLa * t))) - 0 - 0 *
        (Cstar - (Cstar - C₀) * exp (-kLa * t))) (Icc 0 T) t := by
  have h := ((((hasDerivAt_id t).const_mul (-kLa)).exp).const_mul (Cstar - C₀)).const_sub Cstar
  refine h.hasDerivWithinAt.congr_deriv ?_
  simp only [id_eq, mul_one]
  ring

/-- Aeration from any `C₀ ∈ [0, C*]` stays in `[0, C*]`. -/
example {kLa Cstar C₀ T : ℝ} (hkLa : 0 < kLa) (hC₀ : C₀ ∈ Icc 0 Cstar) :
    ∀ t ∈ Icc 0 T, Cstar - (Cstar - C₀) * exp (-kLa * t) ∈ Icc 0 Cstar := by
  refine (balance (u := fun _ ↦ 0) (D := fun _ ↦ 0) hkLa (fun _ _ ↦ le_rfl)
    (fun _ _ ↦ le_rfl) (fun t _ ↦ hasDerivWithinAt_aeration kLa Cstar C₀ T t)).1
    (fun _ _ ↦ mul_nonneg hkLa.le (hC₀.1.trans hC₀.2)) ?_
  simpa using hC₀

/-- The same through `mem_Icc_of_uptake_le_transfer`, with `kLa ≥ 0` only. With the namespace
open, `mem_Icc` is still Mathlib's `Set.mem_Icc`. -/
example {kLa Cstar C₀ T : ℝ} (hkLa : 0 ≤ kLa) (hC₀ : 0 ≤ C₀) (hC₀' : C₀ ≤ Cstar) :
    ∀ t ∈ Icc 0 T, Cstar - (Cstar - C₀) * exp (-kLa * t) ∈ Icc 0 Cstar :=
  mem_Icc_of_uptake_le_transfer (u := fun _ ↦ 0) (D := fun _ ↦ 0) hkLa (fun _ _ ↦ le_rfl)
    (fun _ _ ↦ le_rfl) (fun t _ ↦ hasDerivWithinAt_aeration kLa Cstar C₀ T t)
    (fun _ _ ↦ mul_nonneg hkLa (hC₀.trans hC₀'))
    (mem_Icc.mpr ⟨by simpa using hC₀, by simpa using hC₀'⟩)

/-- With `K_L a = 2`, `C* = 3`, `u = 1` and `D = 1`, the equilibrium is
`C_eq = (2 * 3 - 1) / (2 + 1) = 5 / 3`, and the constant solution `C = 5 / 3` solves the balance. -/
theorem hasDerivWithinAt_equilibrium (T t : ℝ) :
    HasDerivWithinAt (fun _ ↦ (5 / 3 : ℝ)) (2 * (3 - 5 / 3) - 1 - 1 * (5 / 3)) (Icc 0 T) t := by
  convert hasDerivWithinAt_const t (Icc 0 T) (5 / 3 : ℝ) using 1
  norm_num

/-- The equilibrium itself meets the critical-oxygen condition with equality: `C_crit = C_eq`. -/
example {T : ℝ} : ∀ t ∈ Icc 0 T, (5 / 3 : ℝ) ≤ (fun _ ↦ (5 / 3 : ℝ)) t :=
  (balance (u := fun _ ↦ 1) (D := fun _ ↦ 1) (by norm_num)
    (fun _ _ ↦ zero_le_one) (fun _ _ ↦ zero_le_one)
    (fun t _ ↦ hasDerivWithinAt_equilibrium T t)).2.1 _ le_rfl (fun _ _ ↦ by norm_num)

/-- For constant inputs the critical-oxygen condition is `C_eq ≥ C_crit`: here `C_crit = 3 / 2`
passes and `C_crit = 2` fails, as `C_eq = 5 / 3`. -/
example : (1 : ℝ) + 1 * (3 / 2) ≤ 2 * (3 - 3 / 2) :=
  (uptake_add_dilution_le_transfer_iff (by norm_num) (by norm_num)).mpr (by norm_num)

example : ¬ (1 : ℝ) + 1 * 2 ≤ 2 * (3 - 2) := fun h ↦ by
  have := (uptake_add_dilution_le_transfer_iff (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) ≤ 1)).mp h
  norm_num at this

/-- The constant-input clause of the balance, on a horizon `[0, 1]`. -/
example : ((∀ t ∈ Icc (0 : ℝ) 1, (fun _ ↦ (1 : ℝ)) t + (fun _ ↦ (1 : ℝ)) t * (3 / 2) ≤
    2 * (3 - 3 / 2)) ↔ (3 / 2 : ℝ) ≤ (2 * 3 - 1) / (2 + 1)) :=
  (balance (u := fun _ ↦ 1) (D := fun _ ↦ 1) (by norm_num)
    (fun _ _ ↦ zero_le_one) (fun _ _ ↦ zero_le_one)
    (fun t _ ↦ hasDerivWithinAt_equilibrium 1 t)).2.2 1 1 (3 / 2) zero_le_one
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Boundary case `u = K_L a C*` with any dilution: oxygen-free liquid stays oxygen-free, so the
lower end of `[0, C*]` is attained. -/
example {kLa Cstar T : ℝ} {D : ℝ → ℝ} (hkLa : 0 < kLa) (hCstar : 0 ≤ Cstar)
    (hD : ∀ t ∈ Icc 0 T, 0 ≤ D t) : ∀ t ∈ Icc 0 T, (fun _ ↦ (0 : ℝ)) t ∈ Icc 0 Cstar :=
  (balance (u := fun _ ↦ kLa * Cstar) hkLa
    (fun _ _ ↦ mul_nonneg hkLa.le hCstar) hD
    (fun t _ ↦ by
      convert hasDerivWithinAt_const t (Icc 0 T) (0 : ℝ) using 1
      ring)).1 (fun _ _ ↦ le_rfl) ⟨le_rfl, hCstar⟩

/-- The uptake bound cannot be dropped: with `K_L a = 1`, `C* = 1`, `D = 0` and `u = 2 > K_L a C*`,
the solution `C(t) = e^{-t} - 1` of `C' = (1 - C) - 2` starts at `0` and is negative at `t = 1`. -/
example : (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s ↦ exp (-s) - 1)
      (1 * (1 - (exp (-t) - 1)) - 2 - 0 * (exp (-t) - 1)) (Icc 0 1) t) ∧
    exp (-0) - 1 ∈ Icc (0 : ℝ) 1 ∧ exp (-1) - 1 < 0 := by
  refine ⟨fun t _ ↦ ?_, by simp, ?_⟩
  · refine (((hasDerivAt_neg t).exp).sub_const 1).hasDerivWithinAt.congr_deriv ?_
    ring
  · have := exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)
    linarith

end DomainsTest.Chemistry.Bioreactors.DissolvedOxygen
