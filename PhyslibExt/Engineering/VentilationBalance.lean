/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.ODE.ConstantInputRelaxation
import Mathlib.Tactic.FieldSimp

/-!
# Well-mixed ventilation balance

## i. Overview

A well-mixed room of constant volume `V` with volumetric flow `Q`,
outdoor concentration `c_out`, constant indoor source `G`, and no
reactive sink is a one-compartment balance: with the canonical
compartment `amount` from
`MathlibExt.Analysis.ODE.ConstantInputRelaxation`, the indoor
concentration is `amount (Q / V) ((Q * c_out + G) / V) c0 t`. Its
equilibrium is `c_out + G / Q` (meaningful for `Q > 0`).
Concentrations are mass per volume in one consistent unit; a ppm
figure is not a mass concentration and must be converted with the
gas density first (see the companion tests). This module
transports the compartment explicit solution, balance, envelope,
sign, and limit facts under that parameter mapping; it proves no
new ODE solution and states no health threshold, reactive sink,
or variable-volume model.

## ii. Key results

- `Engineering.VentilationBalance.ventilationConcentration`: the
  well-mixed concentration as a compartment amount.
- `Engineering.VentilationBalance.steadyAmount_eq_ventilationEquilibrium`:
  the compartment steady amount at the mapped parameters is the
  ventilation equilibrium.
- `Engineering.VentilationBalance.ventilationConcentration_eq_explicit` and
  `ventilationConcentration_hasDerivAt`: the exponential profile
  and the CSTR-form balance `c' = (Q / V) (c_out - c) + G / V`.
- `Engineering.VentilationBalance.ventilationConcentration_le_equilibrium`,
  `ventilationConcentration_ge_equilibrium`,
  `ventilationConcentration_nonneg`, and
  `ventilationConcentration_tendsto_equilibrium`: the transported
  envelope, sign, and limit.

## iii. Table of contents

- A. Equilibrium and the amount-parameterized concentration
- B. Transported concentration results
- C. Ventilation concentration from the canonical amount

## iv. References

- `MathlibExt.Analysis.ODE.ConstantInputRelaxation` for the
  compartment amount, steady amount, explicit formula, envelope,
  and limit facts.
- `PhyslibExt.EarthScience.Reactors` for the CSTR balance whose
  zero-reaction form this matches.
- Standard well-mixed ventilation balance: `V c' = Q (c_out - c) + G`.
-/

@[expose] public section

open Real Filter Topology
open MathlibExt.Biology.Biophysics.CompartmentKinetics

namespace Engineering.VentilationBalance

/-! ## A. Equilibrium and the amount-parameterized concentration -/

/-- Well-mixed ventilation equilibrium concentration for outdoor
concentration `c_out`, constant indoor source strength `G` (mass per
time), and volumetric flow `Q`: `c_out + G / Q`. Concentrations are
in one consistent unit (mass per volume); a ppm figure must be
converted before it is used here. -/
noncomputable def ventilationEquilibrium (Q c_out G : ℝ) : ℝ :=
  c_out + G / Q

/-- Well-mixed ventilation concentration, expressed through a
canonical one-compartment amount function `A` (arguments
`A k R A₀ t`: elimination rate, constant input rate, initial value,
time). The ventilation exchange rate is `k = Q / V` and the input
rate is `R = (Q * c_out + G) / V`, for room volume `V`, flow `Q`,
outdoor concentration `c_out`, indoor source `G`, and initial
concentration `c0`. Constant volume and flow; no reactive sink. -/
private noncomputable def ventilationConcentrationOf
    (A : ℝ → ℝ → ℝ → ℝ → ℝ) (V Q c_out G c0 t : ℝ) : ℝ :=
  A (Q / V) ((Q * c_out + G) / V) c0 t

private lemma equilibrium_bridge {V Q : ℝ} (hV : 0 < V) (hQ : 0 < Q)
    (c_out G : ℝ) :
    ((Q * c_out + G) / V) / (Q / V) = ventilationEquilibrium Q c_out G := by
  have hV' : V ≠ 0 := ne_of_gt hV
  have hQ' : Q ≠ 0 := ne_of_gt hQ
  unfold ventilationEquilibrium
  field_simp

/-- With positive flow and no indoor source, the equilibrium
is the outdoor concentration. (At zero flow every constant
concentration is an equilibrium of the balance, so the
positive-flow domain is part of the claim.) -/
theorem ventilationEquilibrium_zero_source {Q : ℝ} (_hQ : 0 < Q)
    (c_out : ℝ) :
    ventilationEquilibrium Q c_out 0 = c_out := by
  simp [ventilationEquilibrium]


/-! ## B. Transported concentration results -/

/-- Explicit exponential form, transported from the canonical
amount formula at nonzero rate: the concentration is the
equilibrium plus the initial excess decayed at rate `Q / V`. -/
private lemma ventilationConcentration_eq_explicit_of
    {A : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hA : ∀ {k : ℝ}, k ≠ 0 → ∀ R A₀ t : ℝ,
      A k R A₀ t = R / k + (A₀ - R / k) * Real.exp (-k * t))
    {V Q : ℝ} (hV : 0 < V) (hQ : 0 < Q) (c_out G c0 t : ℝ) :
    ventilationConcentrationOf A V Q c_out G c0 t
      = ventilationEquilibrium Q c_out G
        + (c0 - ventilationEquilibrium Q c_out G)
          * Real.exp (-(Q / V) * t) := by
  have hk : Q / V ≠ 0 := div_ne_zero hQ.ne' hV.ne'
  change A (Q / V) ((Q * c_out + G) / V) c0 t
      = ventilationEquilibrium Q c_out G
        + (c0 - ventilationEquilibrium Q c_out G)
          * Real.exp (-(Q / V) * t)
  rw [hA hk, equilibrium_bridge hV hQ c_out G]

/-- The ventilation balance in CSTR form, transported from the
canonical amount derivative: the rate of change is the flow term
`(Q / V) * (c_out - c)` plus the indoor source term `G / V`. -/
private lemma ventilationConcentration_hasDerivAt_of
    {A : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hA : ∀ k R A₀ t : ℝ,
      HasDerivAt (A k R A₀) (R - k * A k R A₀ t) t)
    {V : ℝ} (hV : V ≠ 0) (Q c_out G c0 t : ℝ) :
    HasDerivAt (ventilationConcentrationOf A V Q c_out G c0)
      ((Q / V) * (c_out - ventilationConcentrationOf A V Q c_out G c0 t)
        + G / V) t := by
  have h := hA (Q / V) ((Q * c_out + G) / V) c0 t
  have hval : (Q * c_out + G) / V - (Q / V) * A (Q / V) ((Q * c_out + G) / V) c0 t
      = (Q / V) * (c_out - A (Q / V) ((Q * c_out + G) / V) c0 t) + G / V := by
    field_simp
    ring
  rw [hval] at h
  exact h

/-- Initial value, transported from the canonical amount initial
value. -/
private lemma ventilationConcentration_zero_of
    {A : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hA : ∀ k R A₀ : ℝ, A k R A₀ 0 = A₀)
    (V Q c_out G c0 : ℝ) :
    ventilationConcentrationOf A V Q c_out G c0 0 = c0 := by
  exact hA _ _ _

/-- Starting at the equilibrium keeps the concentration at the
equilibrium, transported from the canonical amount formula. -/
private lemma ventilationConcentration_at_equilibrium_of
    {A : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hA : ∀ {k : ℝ}, k ≠ 0 → ∀ R A₀ t : ℝ,
      A k R A₀ t = R / k + (A₀ - R / k) * Real.exp (-k * t))
    {V Q : ℝ} (hV : 0 < V) (hQ : 0 < Q) (c_out G t : ℝ) :
    ventilationConcentrationOf A V Q c_out G
        (ventilationEquilibrium Q c_out G) t
      = ventilationEquilibrium Q c_out G := by
  have hk : Q / V ≠ 0 := div_ne_zero hQ.ne' hV.ne'
  change A (Q / V) ((Q * c_out + G) / V) (ventilationEquilibrium Q c_out G) t
      = ventilationEquilibrium Q c_out G
  rw [hA hk, equilibrium_bridge hV hQ c_out G]
  simp

/-- Starting below the equilibrium stays below it, transported
from the canonical amount envelope. -/
private lemma ventilationConcentration_le_equilibrium_of
    {A : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hA : ∀ {k R A₀ : ℝ}, 0 < k → A₀ ≤ R / k → ∀ t : ℝ,
      A k R A₀ t ≤ R / k)
    {V Q c_out G c0 : ℝ} (hV : 0 < V) (hQ : 0 < Q)
    (h : c0 ≤ ventilationEquilibrium Q c_out G) (t : ℝ) :
    ventilationConcentrationOf A V Q c_out G c0 t
      ≤ ventilationEquilibrium Q c_out G := by
  have hk : 0 < Q / V := div_pos hQ hV
  rw [← equilibrium_bridge hV hQ c_out G] at h ⊢
  exact hA hk h t

/-- Starting above the equilibrium stays above it, transported
from the canonical amount envelope. -/
private lemma ventilationConcentration_ge_equilibrium_of
    {A : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hA : ∀ {k R A₀ : ℝ}, 0 < k → R / k ≤ A₀ → ∀ t : ℝ,
      R / k ≤ A k R A₀ t)
    {V Q c_out G c0 : ℝ} (hV : 0 < V) (hQ : 0 < Q)
    (h : ventilationEquilibrium Q c_out G ≤ c0) (t : ℝ) :
    ventilationEquilibrium Q c_out G
      ≤ ventilationConcentrationOf A V Q c_out G c0 t := by
  have hk : 0 < Q / V := div_pos hQ hV
  rw [← equilibrium_bridge hV hQ c_out G] at h ⊢
  exact hA hk h t

/-- Nonnegative data give a nonnegative concentration for
nonnegative times, transported from the canonical amount sign. -/
private lemma ventilationConcentration_nonneg_of
    {A : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hA : ∀ {k R A₀ t : ℝ}, 0 ≤ k → 0 ≤ R → 0 ≤ A₀ → 0 ≤ t →
      0 ≤ A k R A₀ t)
    {V Q c_out G c0 t : ℝ} (hV : 0 < V) (hQ : 0 ≤ Q)
    (hc : 0 ≤ c_out) (hG : 0 ≤ G) (hc0 : 0 ≤ c0) (ht : 0 ≤ t) :
    0 ≤ ventilationConcentrationOf A V Q c_out G c0 t := by
  change 0 ≤ A (Q / V) ((Q * c_out + G) / V) c0 t
  exact hA (div_nonneg hQ hV.le)
    (div_nonneg (add_nonneg (mul_nonneg hQ hc) hG) hV.le) hc0 ht

/-- The concentration tends to the equilibrium, transported from
the canonical amount limit. -/
private lemma ventilationConcentration_tendsto_equilibrium_of
    {A : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hA : ∀ {k : ℝ}, 0 < k → ∀ R A₀ : ℝ,
      Tendsto (A k R A₀) atTop (𝓝 (R / k)))
    {V Q : ℝ} (hV : 0 < V) (hQ : 0 < Q) (c_out G c0 : ℝ) :
    Tendsto (ventilationConcentrationOf A V Q c_out G c0) atTop
      (𝓝 (ventilationEquilibrium Q c_out G)) := by
  have hk : 0 < Q / V := div_pos hQ hV
  have hlim := hA hk ((Q * c_out + G) / V) c0
  rw [equilibrium_bridge hV hQ c_out G] at hlim
  exact hlim

/-! ## C. Ventilation concentration from the canonical amount -/

/-- Well-mixed ventilation concentration: the canonical
one-compartment amount at exchange rate `Q / V` and input rate
`(Q * c_out + G) / V`. -/
noncomputable def ventilationConcentration (V Q c_out G c0 t : ℝ) : ℝ :=
  amount (Q / V) ((Q * c_out + G) / V) c0 t


/-- The compartment steady amount at the mapped parameters is
the ventilation equilibrium. -/
theorem steadyAmount_eq_ventilationEquilibrium {V Q : ℝ}
    (hV : 0 < V) (hQ : 0 < Q) (c_out G : ℝ) :
    steadyAmount (Q / V) ((Q * c_out + G) / V)
      = ventilationEquilibrium Q c_out G :=
  equilibrium_bridge hV hQ c_out G

/-- Explicit exponential form: the concentration is the
equilibrium plus the initial excess decayed at rate `Q / V`. -/
theorem ventilationConcentration_eq_explicit {V Q : ℝ}
    (hV : 0 < V) (hQ : 0 < Q) (c_out G c0 t : ℝ) :
    ventilationConcentration V Q c_out G c0 t
      = ventilationEquilibrium Q c_out G
        + (c0 - ventilationEquilibrium Q c_out G)
          * Real.exp (-(Q / V) * t) :=
  ventilationConcentration_eq_explicit_of amount_eq_of_ne_zero hV hQ
    c_out G c0 t

/-- The ventilation balance in CSTR form: the rate of change is
the flow term `(Q / V) * (c_out - c)` plus the indoor source
term `G / V`. -/
theorem ventilationConcentration_hasDerivAt {V : ℝ} (hV : V ≠ 0)
    (Q c_out G c0 t : ℝ) :
    HasDerivAt (ventilationConcentration V Q c_out G c0)
      ((Q / V) * (c_out - ventilationConcentration V Q c_out G c0 t)
        + G / V) t :=
  ventilationConcentration_hasDerivAt_of hasDerivAt_amount hV Q c_out G
    c0 t

/-- Initial value of the ventilation concentration. -/
theorem ventilationConcentration_zero (V Q c_out G c0 : ℝ) :
    ventilationConcentration V Q c_out G c0 0 = c0 :=
  ventilationConcentration_zero_of amount_zero V Q c_out G c0

/-- Starting at the equilibrium keeps the concentration at the
equilibrium. -/
theorem ventilationConcentration_at_equilibrium {V Q : ℝ}
    (hV : 0 < V) (hQ : 0 < Q) (c_out G t : ℝ) :
    ventilationConcentration V Q c_out G
        (ventilationEquilibrium Q c_out G) t
      = ventilationEquilibrium Q c_out G :=
  ventilationConcentration_at_equilibrium_of amount_eq_of_ne_zero hV hQ
    c_out G t

/-- Starting below the equilibrium stays below it. -/
theorem ventilationConcentration_le_equilibrium
    {V Q c_out G c0 : ℝ} (hV : 0 < V) (hQ : 0 < Q)
    (h : c0 ≤ ventilationEquilibrium Q c_out G) (t : ℝ) :
    ventilationConcentration V Q c_out G c0 t
      ≤ ventilationEquilibrium Q c_out G :=
  ventilationConcentration_le_equilibrium_of
    (fun hk h t => amount_le_steadyAmount hk h t) hV hQ h t

/-- Starting above the equilibrium stays above it. -/
theorem ventilationConcentration_ge_equilibrium
    {V Q c_out G c0 : ℝ} (hV : 0 < V) (hQ : 0 < Q)
    (h : ventilationEquilibrium Q c_out G ≤ c0) (t : ℝ) :
    ventilationEquilibrium Q c_out G
      ≤ ventilationConcentration V Q c_out G c0 t :=
  ventilationConcentration_ge_equilibrium_of
    (fun hk h t => steadyAmount_le_amount hk h t) hV hQ h t

/-- Nonnegative data give a nonnegative concentration for
nonnegative times. -/
theorem ventilationConcentration_nonneg {V Q c_out G c0 t : ℝ}
    (hV : 0 < V) (hQ : 0 ≤ Q) (hc : 0 ≤ c_out) (hG : 0 ≤ G)
    (hc0 : 0 ≤ c0) (ht : 0 ≤ t) :
    0 ≤ ventilationConcentration V Q c_out G c0 t :=
  ventilationConcentration_nonneg_of amount_nonneg hV hQ hc hG hc0 ht

/-- The concentration tends to the equilibrium. -/
theorem ventilationConcentration_tendsto_equilibrium {V Q : ℝ}
    (hV : 0 < V) (hQ : 0 < Q) (c_out G c0 : ℝ) :
    Tendsto (ventilationConcentration V Q c_out G c0) atTop
      (𝓝 (ventilationEquilibrium Q c_out G)) :=
  ventilationConcentration_tendsto_equilibrium_of tendsto_amount hV hQ
    c_out G c0

end Engineering.VentilationBalance
