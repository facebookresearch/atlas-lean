/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.IntermediateValue
public import PhyslibExt.Chemistry.Thermodynamics.Entropy

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Renewable energy ports: solar-thermal receiver balance

## i. Overview

An ideal solar-thermal receiver at absorber temperature `T` loses
`U * (T - Ta)` linearly and `K * (T^4 - Ta^4)` radiatively against
ambient `Ta`, and absorbs flux `α * G`. This file proves existence and
uniqueness of the stagnation temperature where the loss balances the
absorbed flux, and the endpoint values of the ideal receiver-engine
objective `η(T) * carnotEfficiency Ta T`. The interior-maximum statement for
that objective on `[Ta, Tstag]` is the compactness argument over these
endpoint and monotonicity facts; no empirical adequacy of the ideal
model is claimed.

## ii. Key results

- `RenewableEnergyPorts.receiver_stagnationTemperature`: for
  `Ta, G > 0`, `α ∈ (0, 1]`, `U ≥ 0`, `K > 0` there is a unique
  `Tstag > Ta` with `receiverLoss U K Ta Tstag = α * G`.
- `RenewableEnergyPorts.receiverLoss_strictMonoOn`: the loss is
  strictly increasing on `[Ta, ∞)` for `Ta ≥ 0`.

## iii. Table of contents

- A. Receiver loss and stagnation temperature

## iv. References

- J. A. Duffie and W. A. Beckman, *Solar Engineering of
  Thermal Processes*, 4th edition (Wiley, 2013), Chapter 6:
  the flat-plate collector balance between absorbed irradiance
  `α * G` and losses `U * (T - Ta)` linear in the temperature
  difference, with stagnation at zero useful output. The
  radiative term `K * (T^4 - Ta^4)` is the Stefan-Boltzmann
  loss written with coefficient `K` in place of an
  emissivity-area factor times the Stefan-Boltzmann constant,
  and the receiver-engine objective multiplies by the Carnot
  factor `1 - Ta / T` (`Chemistry.Thermodynamics.carnotEfficiency`).
  In this notation `α` is absorptance, `G` irradiance, `U` the
  linear loss coefficient, and `K` the radiative coefficient.
- The radiation-balance root pattern of
  `EarthScience.planetaryEnergyBalance_equilibrium_exists` in
  `PhyslibExt.EarthScience.PlanetaryEnergyBalance`, specialized here
  to the receiver loss with a linear term.

## A. Receiver loss and stagnation temperature

-/

@[expose] public section

namespace RenewableEnergyPorts

/-- Receiver loss at absorber temperature `T`: linear loss
`U * (T - Ta)` plus radiative loss `K * (T^4 - Ta^4)`, against ambient
`Ta`. -/
noncomputable def receiverLoss (U K Ta T : ℝ) : ℝ :=
  U * (T - Ta) + K * (T ^ 4 - Ta ^ 4)

/-- Receiver efficiency at temperature `T` for absorbed flux `α * G`:
`η(T) = (α * G - loss(T)) / G`, stated in the multiplied form
`G * η(T) = α * G - loss(T)` by the theorems below. -/
noncomputable def receiverEfficiency (α G U K Ta T : ℝ) : ℝ :=
  (α * G - receiverLoss U K Ta T) / G

/-- Multiplied balance form of the efficiency: for `G ≠ 0`,
`G * η(T) = α * G - loss(T)`. -/
lemma receiverEfficiency_mul {α G U K Ta T : ℝ} (hG : G ≠ 0) :
    G * receiverEfficiency α G U K Ta T = α * G - receiverLoss U K Ta T := by
  unfold receiverEfficiency
  field_simp

/-- The loss vanishes at ambient temperature. -/
lemma receiverLoss_ambient (U K Ta : ℝ) : receiverLoss U K Ta Ta = 0 := by
  unfold receiverLoss
  ring

/-- The loss is strictly increasing on `[Ta, ∞)` for `U ≥ 0`, `K > 0`:
if `Ta ≤ s ≤ t` and `s < t` then `loss(s) < loss(t)`. -/
lemma receiverLoss_strictMonoOn {U K Ta : ℝ} (hU : 0 ≤ U) (hK : 0 < K)
    (hTa : 0 ≤ Ta) :
    StrictMonoOn (receiverLoss U K Ta) (Set.Ici Ta) := by
  intro s hs t ht hlt
  have hs' : Ta ≤ s := hs
  have hst : s ≤ t := hlt.le
  unfold receiverLoss
  have hs0 : 0 ≤ s := le_trans hTa hs'
  have hpow : s ^ 4 < t ^ 4 := pow_lt_pow_left₀ hlt hs0 (by norm_num)
  have hUle : U * (s - Ta) ≤ U * (t - Ta) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hst Ta) hU
  have hKlt : K * (s ^ 4 - Ta ^ 4) < K * (t ^ 4 - Ta ^ 4) :=
    mul_lt_mul_of_pos_left (sub_lt_sub_right hpow (Ta ^ 4)) hK
  exact add_lt_add_of_le_of_lt hUle hKlt

/-- A dimensionally valid large-temperature bound: at
`Ta + 2 * sqrt (sqrt (α * G / K))` the loss exceeds `α * G`
whenever `U ≥ 0`, `K > 0`, `Ta ≥ 0`, and `α * G > 0`. The
fourth root `q = (α * G / K)^{1/4}` has units of temperature,
matching `Ta`, and the increment `2 * q` is a dimensionless
multiple of that temperature; the radiative term alone
dominates because `(Ta + d)^4 - Ta^4 ≥ d^4` for
`d = 2 * (α * G / K)^{1/4}`, with `d^4 = 16 * (α * G / K)`. -/
lemma receiverLoss_gt_at_large {U K Ta α G : ℝ} (hU : 0 ≤ U) (hK : 0 < K)
    (hTa : 0 ≤ Ta) (hαG : 0 < α * G) :
    α * G < receiverLoss U K Ta
      (Ta + 2 * (Real.sqrt (Real.sqrt (α * G / K)))) := by
  set q : ℝ := Real.sqrt (Real.sqrt (α * G / K)) with hq
  have hKne : K ≠ 0 := ne_of_gt hK
  have hαGK : (0 : ℝ) ≤ α * G / K := div_nonneg (le_of_lt hαG) (le_of_lt hK)
  have hq_nn : (0 : ℝ) ≤ q := Real.sqrt_nonneg _
  have hq_pos : 0 < q := by
    rw [hq]
    exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (div_pos hαG hK))
  have hd_nn : (0 : ℝ) ≤ 2 * q := by linarith
  have hq4 : q ^ 4 = α * G / K := by
    have h1 : q ^ 2 = Real.sqrt (α * G / K) := by
      rw [hq]
      exact Real.sq_sqrt (Real.sqrt_nonneg _)
    calc q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (α * G / K)) ^ 2 := by rw [h1]
      _ = α * G / K := Real.sq_sqrt hαGK
  have hq4lt : q ^ 4 < (2 * q) ^ 4 :=
    pow_lt_pow_left₀ (by linarith) hq_nn (by norm_num)
  have hexpand : (Ta + (2 * q)) ^ 4 - Ta ^ 4
      = 4 * Ta ^ 3 * (2 * q) + 6 * Ta ^ 2 * (2 * q) ^ 2
        + 4 * Ta * (2 * q) ^ 3 + (2 * q) ^ 4 := by ring
  have hrad : (2 * q) ^ 4 ≤ (Ta + (2 * q)) ^ 4 - Ta ^ 4 := by
    rw [hexpand]
    have t1 : (0 : ℝ) ≤ 4 * Ta ^ 3 * (2 * q) :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hTa 3)) hd_nn
    have t2 : (0 : ℝ) ≤ 6 * Ta ^ 2 * (2 * q) ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hTa 2)) (sq_nonneg _)
    have t3 : (0 : ℝ) ≤ 4 * Ta * (2 * q) ^ 3 :=
      mul_nonneg (mul_nonneg (by norm_num) hTa) (pow_nonneg hd_nn 3)
    linarith
  have hKgt : α * G < K * ((Ta + (2 * q)) ^ 4 - Ta ^ 4) := by
    have h1 : K * (α * G / K) = α * G := by
      rw [mul_comm K (α * G / K)]
      exact div_mul_cancel₀ _ hKne
    have h2 : K * (α * G / K) < K * ((Ta + (2 * q)) ^ 4 - Ta ^ 4) :=
      mul_lt_mul_of_pos_left (lt_of_lt_of_le (by rwa [hq4] at hq4lt) hrad) hK
    rwa [h1] at h2
  have hUd : (0 : ℝ) ≤ U * (2 * q) := mul_nonneg hU hd_nn
  unfold receiverLoss
  have hsub : Ta + 2 * (Real.sqrt (Real.sqrt (α * G / K))) - Ta
      = 2 * q := by
    rw [hq]
    ring
  rw [hsub]
  linarith

/-- Stagnation temperature existence and uniqueness: for `Ta, G > 0`,
`α ∈ (0, 1]`, `U ≥ 0`, `K > 0`, there is a unique `Tstag > Ta` with
`loss(Tstag) = α * G`. -/
lemma receiver_stagnationTemperature {Ta G α U K : ℝ} (hTa : 0 < Ta)
    (hG : 0 < G) (hα0 : 0 < α) (hα1 : α ≤ 1) (hU : 0 ≤ U) (hK : 0 < K) :
    ∃! Tstag : ℝ, Ta < Tstag ∧ receiverLoss U K Ta Tstag = α * G := by
  have _ := hα1
  have hαG : 0 < α * G := mul_pos hα0 hG
  have hpos : 0 < α * G / K := div_pos hαG hK
  have hle : Ta ≤ Ta + 2 * (Real.sqrt (Real.sqrt (α * G / K))) := by
    have hnn : (0 : ℝ) ≤ Real.sqrt (Real.sqrt (α * G / K)) :=
      Real.sqrt_nonneg _
    linarith
  have hgt : α * G < receiverLoss U K Ta (Ta + 2 * (Real.sqrt (Real.sqrt (α * G / K)))) :=
    receiverLoss_gt_at_large hU hK hTa.le hαG
  have hcont : ContinuousOn (fun T => receiverLoss U K Ta T)
      (Set.Icc Ta (Ta + 2 * (Real.sqrt (Real.sqrt (α * G / K))))) := by
    have hfc : Continuous (fun T => receiverLoss U K Ta T) := by
      unfold receiverLoss
      continuity
    exact hfc.continuousOn
  have hmem : α * G ∈ (fun T => receiverLoss U K Ta T) ''
      Set.Ioo Ta (Ta + 2 * (Real.sqrt (Real.sqrt (α * G / K)))) := by
    have hsub := intermediate_value_Ioo hle hcont
    apply hsub
    constructor
    · show receiverLoss U K Ta Ta < α * G
      rw [receiverLoss_ambient]
      exact hαG
    · show α * G < receiverLoss U K Ta (Ta + 2 * (Real.sqrt (Real.sqrt (α * G / K))))
      exact hgt
  obtain ⟨Tstag, hIoo, hval⟩ := hmem
  dsimp only at hval
  refine ⟨Tstag, ⟨hIoo.1, hval⟩, ?_⟩
  intro y hy
  rcases lt_trichotomy y Tstag with h | h | h
  · exfalso
    have hlt := receiverLoss_strictMonoOn hU hK hTa.le (Set.mem_Ici.mpr hy.1.le) (Set.mem_Ici.mpr hIoo.1.le) h
    rw [hy.2, hval] at hlt
    exact lt_irrefl _ hlt
  · exact h
  · exfalso
    have hlt := receiverLoss_strictMonoOn hU hK hTa.le (Set.mem_Ici.mpr hIoo.1.le) (Set.mem_Ici.mpr hy.1.le) h
    rw [hval, hy.2] at hlt
    exact lt_irrefl _ hlt

/-- The ideal receiver-engine objective: receiver efficiency times
the Carnot factor `carnotEfficiency Ta T = 1 - Ta / T` from
`Chemistry.Thermodynamics`. -/
noncomputable def receiverObjective (α G U K Ta T : ℝ) : ℝ :=
  receiverEfficiency α G U K Ta T *
    Chemistry.Thermodynamics.carnotEfficiency Ta T

/-- The receiver objective vanishes at both endpoints `T = Ta`
and at any stagnation temperature `Tstag` with
`loss(Tstag) = α * G` (for `G ≠ 0`, `Tstag ≠ 0`). -/
lemma receiver_objective_endpoints {Ta G α U K Tstag : ℝ} (hG : G ≠ 0)
    (hTa : Ta ≠ 0) (hT : Tstag ≠ 0) (hstag : receiverLoss U K Ta Tstag = α * G) :
    receiverObjective α G U K Ta Ta = 0 ∧
      receiverObjective α G U K Ta Tstag = 0 := by
  have _ := hG
  have _ := hT
  have hTa1 : Ta / Ta = 1 := div_self hTa
  constructor
  · unfold receiverObjective Chemistry.Thermodynamics.carnotEfficiency
    rw [hTa1, sub_self, mul_zero]
  · have heff : receiverEfficiency α G U K Ta Tstag = 0 := by
      unfold receiverEfficiency
      rw [hstag, sub_self, zero_div]
    unfold receiverObjective
    rw [heff, zero_mul]

end RenewableEnergyPorts
