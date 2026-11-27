/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.ODE.ConstantInputRelaxation
import PhyslibExt.Chemistry.ReactingTransportPorts

/-!
# Dimensionless adiabatic stirred-tank reactor

Steady-state reduction, scalar energy balance, and global forward bounds for an adiabatic reactor.

## i. Overview

With unit dilution and unit feed concentration and temperature, the Arrhenius rate is
`exp (a - b / T)`. The heat-release term in the temperature equation cancels the reaction
term in `β` times the concentration equation. The resulting scalar relaxation of
`T + β * c` gives an upper temperature bound independent of the Arrhenius prefactor.
It can be tighter than the general Arrhenius box bound, but neither bound is uniformly tighter.

The forward path assumes `b > 0`, `β ≥ 0`, `c₀ ∈ [0, 1]`, and `T₀ > 0`. The algebraic
and derivative identities use the total real-valued rate expression; only `T > 0`
is physical.

## ii. Key results

- `Chemistry.AdiabaticReactor.steady_states_and_energy_invariant`: a scalar equation
  characterizes the steady-state temperature, `T + β * c` satisfies a scalar relaxation
  equation, and a global forward path stays in the stated concentration and temperature ranges.

## iii. Table of contents

- A. Steady states
- B. Scalar energy balance
- C. Global forward path and bounds

## iv. References

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*,
  2nd ed., 7th printing, §6.3.1, pp. 288–289, for the steady-state material and adiabatic
  energy balances. The forward bound uses the time-dependent balances.
-/

@[expose] public section

namespace Chemistry.AdiabaticReactor

/-! ## A. Steady states -/

private lemma steady_state (a b β c T : ℝ) :
    (1 - c - Real.exp (a - b / T) * c = 0 ∧
      1 - T + β * Real.exp (a - b / T) * c = 0) ↔
    (c = 1 / (1 + Real.exp (a - b / T)) ∧
      1 + β * Real.exp (a - b / T) / (1 + Real.exp (a - b / T)) - T = 0) := by
  set k := Real.exp (a - b / T)
  have hk : 0 < k := Real.exp_pos _
  have hden : 1 + k ≠ 0 := ne_of_gt (by linarith)
  have hmass : (1 - c - k * c = 0) ↔ c = 1 / (1 + k) := by
    rw [eq_div_iff hden]
    constructor <;> intro h <;> linarith only [h]
  rw [hmass]
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← mul_div_assoc, mul_one] at h
    linarith only [h]
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← mul_div_assoc, mul_one]
    linarith only [h]

/-! ## B. Scalar energy balance -/

private lemma hasDerivAt_energy {a b β : ℝ} {c T : ℝ → ℝ} {t : ℝ}
    (hc : HasDerivAt c (1 - c t - Real.exp (a - b / T t) * c t) t)
    (hT : HasDerivAt T (1 - T t + β * Real.exp (a - b / T t) * c t) t) :
    HasDerivAt (fun s ↦ T s + β * c s) (1 + β - (T t + β * c t)) t :=
  (hT.add (hc.const_mul β)).congr_deriv (by ring)

/-! ## C. Global forward path and bounds -/

open ReactingTransportPorts in
open MathlibExt.Biology.Biophysics.CompartmentKinetics in
private lemma exists_forward_path (a : ℝ) {b β c₀ T₀ : ℝ}
    (hb : 0 < b) (hβ : 0 ≤ β) (hc₀ : c₀ ∈ Set.Icc 0 1) (hT₀ : 0 < T₀) :
    ∃ c T : ℝ → ℝ, c 0 = c₀ ∧ T 0 = T₀ ∧ ∀ t ≥ 0,
      c t ∈ Set.Icc 0 1 ∧ T t ∈ Set.Icc (min T₀ 1) (max (T₀ + β * c₀) (1 + β)) ∧
      HasDerivAt c (1 - c t - Real.exp (a - b / T t) * c t) t ∧
      HasDerivAt T (1 - T t + β * Real.exp (a - b / T t) * c t) t := by
  obtain ⟨c, T, hc0, hT0, hpath⟩ := exists_arrhenius_path
    (a := 1) (A := Real.exp a) (B := b) (b := β) (h := 0) (cin := 1) (Tin := 1) (Tc := 1)
    zero_lt_one hb hT₀ zero_lt_one zero_lt_one (Real.exp_pos _).le hβ le_rfl zero_le_one hc₀.1
  have hrate (x : ℝ) : arrheniusRateConstant (Real.exp a) b x = Real.exp (a - b / x) := by
    rw [arrheniusRateConstant, Real.exp_sub, neg_div, Real.exp_neg, ← div_eq_mul_inv]
  have hbal (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt c (1 - c t - Real.exp (a - b / T t) * c t) t ∧
      HasDerivAt T (1 - T t + β * Real.exp (a - b / T t) * c t) t := by
    simpa only [concentrationRhs, temperatureRhs, hrate, one_mul, zero_mul, sub_zero] using
      (hpath t ht).2
  let Z : ℝ → ℝ := fun t ↦ T t + β * c t
  have hZ : IsSolution 1 (1 + β) Z := by
    intro t ht
    simpa only [one_mul] using hasDerivAt_energy (hbal t ht).1 (hbal t ht).2
  refine ⟨c, T, hc0, hT0, fun t ht ↦ ?_⟩
  have hc : c t ∈ Set.Icc 0 1 := by
    simpa only [concentrationCeiling, max_eq_right hc₀.2] using (hpath t ht).1.1
  have hTlo : min T₀ 1 ≤ T t := by
    simpa [temperatureFloor] using (hpath t ht).1.2.1
  have hZe := hZ.eq_amount ht
  rw [amount_eq_of_ne_zero one_ne_zero] at hZe
  simp only [Z, hc0, hT0, div_one, neg_one_mul] at hZe
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  let M := max (T₀ + β * c₀) (1 + β)
  have hZhi : T t + β * c t ≤ M := calc
    T t + β * c t = (1 - Real.exp (-t)) * (1 + β) + Real.exp (-t) * (T₀ + β * c₀) := by
      rw [hZe]
      ring
    _ ≤ (1 - Real.exp (-t)) * M + Real.exp (-t) * M :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) (sub_nonneg.mpr he))
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_pos _).le)
    _ = M := by ring
  exact ⟨hc, ⟨hTlo, le_trans (le_add_of_nonneg_right (mul_nonneg hβ hc.1)) hZhi⟩, hbal t ht⟩

/-- The dimensionless adiabatic stirred-tank balances with `k(T) = exp (a - b / T)`:
steady states reduce to the scalar temperature equation; `T + β * c` relaxes toward
`1 + β`; and physical initial data admit a global forward path with `0 ≤ c ≤ 1` and
`min T₀ 1 ≤ T ≤ max (T₀ + β * c₀) (1 + β)`. The algebraic and derivative identities
also hold for the total real-valued Lean expressions outside the physical temperature domain. -/
lemma steady_states_and_energy_invariant (a : ℝ) {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) :
    (∀ c T : ℝ,
      (1 - c - Real.exp (a - b / T) * c = 0 ∧
        1 - T + β * Real.exp (a - b / T) * c = 0) ↔
      (c = 1 / (1 + Real.exp (a - b / T)) ∧
        1 + β * Real.exp (a - b / T) / (1 + Real.exp (a - b / T)) - T = 0)) ∧
    (∀ (c T : ℝ → ℝ) (t : ℝ),
      HasDerivAt c (1 - c t - Real.exp (a - b / T t) * c t) t →
      HasDerivAt T (1 - T t + β * Real.exp (a - b / T t) * c t) t →
      HasDerivAt (fun s ↦ T s + β * c s) (1 + β - (T t + β * c t)) t) ∧
    (∀ {c₀ T₀ : ℝ}, c₀ ∈ Set.Icc 0 1 → 0 < T₀ →
      ∃ c T : ℝ → ℝ, c 0 = c₀ ∧ T 0 = T₀ ∧ ∀ t ≥ 0,
        c t ∈ Set.Icc 0 1 ∧ T t ∈ Set.Icc (min T₀ 1) (max (T₀ + β * c₀) (1 + β)) ∧
        HasDerivAt c (1 - c t - Real.exp (a - b / T t) * c t) t ∧
        HasDerivAt T (1 - T t + β * Real.exp (a - b / T t) * c t) t) :=
  ⟨steady_state a b β, fun _ _ _ ↦ hasDerivAt_energy, exists_forward_path a hb hβ⟩

end Chemistry.AdiabaticReactor

end
