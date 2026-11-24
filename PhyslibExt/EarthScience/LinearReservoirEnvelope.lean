/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.CatchmentWaterBalance
public import MathlibExt.Analysis.ODE.ConstantInputRelaxation
import Mathlib.Order.Monotone.Basic

/-!
# Linear-reservoir operating envelope

## i. Overview

The linear reservoir in `PhyslibExt.EarthScience.CatchmentWaterBalance` has
the same explicit profile as the one-compartment amount in
`MathlibExt.Analysis.ODE.ConstantInputRelaxation`, with recession
coefficient `k`, constant inflow `I`, initial storage `S0`, and steady
storage `I / k`. This companion module records that bridge and transports
the compartment envelope facts to storage: nonnegativity in the decay
regime, the two steady-storage bounds, and the supplied-capacity form.
`Smax` is an operating envelope, not a controller. No new reservoir
profile, empirical validation, or control law is introduced.

## ii. Key results

- `EarthScience.linearReservoirStorage_eq_amount`: the reservoir profile
  equals the compartment amount for `k ≠ 0`.
- `EarthScience.linearReservoirStorage_nonneg`: nonnegative data give
  nonnegative storage at nonnegative times.
- `EarthScience.linearReservoirStorage_le_steady` and
  `EarthScience.steady_le_linearReservoirStorage`: the profile stays on
  the initial side of the steady storage.
- `EarthScience.linearReservoirStorage_le_capacity`: storage remains in
  a supplied envelope containing both `S0` and `I / k`.

## iii. Table of contents

- A. Compartment-amount bridge
- B. Transported envelope results

## iv. References

- `PhyslibExt.EarthScience.CatchmentWaterBalance` for the reservoir
  profile and its water budget.
- `MathlibExt.Analysis.ODE.ConstantInputRelaxation` for the compartment
  amount, steady amount, and envelope facts.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Compartment-amount bridge -/

/-- The linear-reservoir storage profile is the one-compartment amount with elimination rate `k`,
constant input `I`, and initial amount `S0`, whenever `k ≠ 0`. The compartment argument order is
`amount k I S0 t`. For `k = 0` the two differ when `I * t ≠ 0`: the storage is `S0`, by the
convention `x / 0 = 0`, while the amount is `S0 + I * t`. -/
theorem linearReservoirStorage_eq_amount {I k : ℝ} (hk : k ≠ 0)
    (S0 t : ℝ) :
    linearReservoirStorage I k S0 t
      = MathlibExt.Biology.Biophysics.CompartmentKinetics.amount k I S0 t := by
  rw [MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_eq_of_ne_zero hk]
  rfl

/-! ## B. Transported envelope results -/

/-- Transported reservoir nonnegativity. The equality and the
amount nonnegativity fact are supplied at Atlas integration from
the canonical compartment-amount definition and theorem; this
lemma performs only the parameter transport `amount k I S0 t`. -/
private lemma linearReservoirStorage_nonneg_of_amount
    {amount : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hEq : ∀ {I k S0 t : ℝ}, k ≠ 0 →
      linearReservoirStorage I k S0 t = amount k I S0 t)
    (hamount_nonneg : ∀ {k R A0 t : ℝ},
      0 ≤ k → 0 ≤ R → 0 ≤ A0 → 0 ≤ t → 0 ≤ amount k R A0 t)
    {I k S0 t : ℝ} (hk : 0 < k) (hI : 0 ≤ I) (hS0 : 0 ≤ S0)
    (ht : 0 ≤ t) :
    0 ≤ linearReservoirStorage I k S0 t := by
  have hk' : k ≠ 0 := ne_of_gt hk
  rw [hEq hk']
  exact hamount_nonneg hk.le hI hS0 ht

/-- Transported upper steady-storage bound. The steady-amount
equality and amount bound are supplied at Atlas integration;
`steadyAmount k I` is the same scalar as `I / k`. -/
private lemma linearReservoirStorage_le_steady_of_amount
    {amount : ℝ → ℝ → ℝ → ℝ → ℝ}
    {steady : ℝ → ℝ → ℝ}
    (hEq : ∀ {I k S0 t : ℝ}, k ≠ 0 →
      linearReservoirStorage I k S0 t = amount k I S0 t)
    (hsteady : ∀ k R : ℝ, steady k R = R / k)
    (hamount_le_steady : ∀ {k R A0 t : ℝ},
      0 < k → A0 ≤ steady k R → amount k R A0 t ≤ steady k R)
    {I k S0 t : ℝ} (hk : 0 < k) (h : S0 ≤ I / k) :
    linearReservoirStorage I k S0 t ≤ I / k := by
  have hk' : k ≠ 0 := ne_of_gt hk
  have hle : S0 ≤ steady k I := by rwa [hsteady k I]
  have hbound : amount k I S0 t ≤ steady k I := hamount_le_steady hk hle
  rw [hsteady k I] at hbound
  rwa [hEq hk']

/-- Transported lower steady-storage bound. The steady-amount
equality and amount bound are supplied at Atlas integration;
`steadyAmount k I` is the same scalar as `I / k`. -/
private lemma steady_le_linearReservoirStorage_of_amount
    {amount : ℝ → ℝ → ℝ → ℝ → ℝ}
    {steady : ℝ → ℝ → ℝ}
    (hEq : ∀ {I k S0 t : ℝ}, k ≠ 0 →
      linearReservoirStorage I k S0 t = amount k I S0 t)
    (hsteady : ∀ k R : ℝ, steady k R = R / k)
    (hsteady_le_amount : ∀ {k R A0 t : ℝ},
      0 < k → steady k R ≤ A0 → steady k R ≤ amount k R A0 t)
    {I k S0 t : ℝ} (hk : 0 < k) (h : I / k ≤ S0) :
    I / k ≤ linearReservoirStorage I k S0 t := by
  have hk' : k ≠ 0 := ne_of_gt hk
  have hge : steady k I ≤ S0 := by rwa [hsteady k I]
  have hbound : steady k I ≤ amount k I S0 t := hsteady_le_amount hk hge
  rw [hsteady k I] at hbound
  rwa [hEq hk']

/-- Transported operating-envelope capacity corollary. Below
the steady storage it uses the supplied amount steady bound;
above the steady storage it uses supplied amount antitonicity
and the amount initial value. `Smax` is a supplied envelope,
not a controller. -/
private lemma linearReservoirStorage_le_capacity_of_amount
    {amount : ℝ → ℝ → ℝ → ℝ → ℝ}
    {steady : ℝ → ℝ → ℝ}
    (hEq : ∀ {I k S0 t : ℝ}, k ≠ 0 →
      linearReservoirStorage I k S0 t = amount k I S0 t)
    (hsteady : ∀ k R : ℝ, steady k R = R / k)
    (hamount_le_steady : ∀ {k R A0 t : ℝ},
      0 < k → A0 ≤ steady k R → amount k R A0 t ≤ steady k R)
    (hamount_antitone : ∀ {k R A0 : ℝ},
      0 < k → steady k R ≤ A0 → Antitone (amount k R A0))
    (hamount_zero : ∀ {k R A0 : ℝ}, amount k R A0 0 = A0)
    {I k S0 Smax t : ℝ} (hk : 0 < k) (ht : 0 ≤ t)
    (hS0 : S0 ≤ Smax) (hcap : I / k ≤ Smax) :
    linearReservoirStorage I k S0 t ≤ Smax := by
  have hk' : k ≠ 0 := ne_of_gt hk
  by_cases hle : S0 ≤ I / k
  · have hle' : S0 ≤ steady k I := by rwa [hsteady k I]
    have hbound : amount k I S0 t ≤ steady k I := hamount_le_steady hk hle'
    rw [hsteady k I] at hbound
    rw [hEq hk']
    exact le_trans hbound hcap
  · have hlt : I / k < S0 := lt_of_not_ge hle
    have hge : steady k I ≤ S0 := by
      rw [hsteady k I]
      exact le_of_lt hlt
    have hanti := hamount_antitone hk hge
    have hmono : amount k I S0 t ≤ amount k I S0 0 := hanti ht
    rw [hamount_zero] at hmono
    rw [hEq hk']
    exact le_trans hmono hS0

/-- Nonnegative inflow and initial storage give nonnegative
storage at every nonnegative time in the decay regime. -/
theorem linearReservoirStorage_nonneg {I k S0 t : ℝ}
    (hk : 0 < k) (hI : 0 ≤ I) (hS0 : 0 ≤ S0) (ht : 0 ≤ t) :
    0 ≤ linearReservoirStorage I k S0 t :=
  linearReservoirStorage_nonneg_of_amount
    (amount := MathlibExt.Biology.Biophysics.CompartmentKinetics.amount)
    (fun hk => linearReservoirStorage_eq_amount hk _ _)
    MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_nonneg
    hk hI hS0 ht

/-- For `k > 0`, starting at or below the steady storage `I / k`, the
profile never exceeds that steady storage. -/
theorem linearReservoirStorage_le_steady {I k S0 t : ℝ}
    (hk : 0 < k) (h : S0 ≤ I / k) :
    linearReservoirStorage I k S0 t ≤ I / k :=
  linearReservoirStorage_le_steady_of_amount
    (amount := MathlibExt.Biology.Biophysics.CompartmentKinetics.amount)
    (steady := MathlibExt.Biology.Biophysics.CompartmentKinetics.steadyAmount)
    (fun hk => linearReservoirStorage_eq_amount hk _ _)
    (fun _ _ => rfl)
    (fun hk h =>
      MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_le_steadyAmount hk h _)
    hk h

/-- For `k > 0`, starting at or above the steady storage `I / k`, the
profile never falls below that steady storage. -/
theorem steady_le_linearReservoirStorage {I k S0 t : ℝ}
    (hk : 0 < k) (h : I / k ≤ S0) :
    I / k ≤ linearReservoirStorage I k S0 t :=
  steady_le_linearReservoirStorage_of_amount
    (amount := MathlibExt.Biology.Biophysics.CompartmentKinetics.amount)
    (steady := MathlibExt.Biology.Biophysics.CompartmentKinetics.steadyAmount)
    (fun hk => linearReservoirStorage_eq_amount hk _ _)
    (fun _ _ => rfl)
    (fun hk h =>
      MathlibExt.Biology.Biophysics.CompartmentKinetics.steadyAmount_le_amount hk h _)
    hk h

/-- Operating-envelope capacity form: for `k > 0` and at nonnegative times, if
both the initial storage and the steady storage are at most
`Smax`, then the storage remains at most `Smax`. The bound
`Smax` is a supplied envelope, not a controller. -/
theorem linearReservoirStorage_le_capacity {I k S0 Smax t : ℝ}
    (hk : 0 < k) (ht : 0 ≤ t) (hS0 : S0 ≤ Smax)
    (hsteady : I / k ≤ Smax) :
    linearReservoirStorage I k S0 t ≤ Smax :=
  linearReservoirStorage_le_capacity_of_amount
    (amount := MathlibExt.Biology.Biophysics.CompartmentKinetics.amount)
    (steady := MathlibExt.Biology.Biophysics.CompartmentKinetics.steadyAmount)
    (fun hk => linearReservoirStorage_eq_amount hk _ _)
    (fun _ _ => rfl)
    (fun hk h =>
      MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_le_steadyAmount hk h _)
    MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_antitone
    (fun {k R A0} =>
      MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_zero k R A0)
    hk ht hS0 hsteady

end EarthScience
