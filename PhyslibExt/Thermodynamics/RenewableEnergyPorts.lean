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

/-- At `Ta` the loss is `0 < α * G`; at `Ta + α * G / K + 1` scaled
point the loss exceeds `α * G`. Precisely: for `α * G > 0`,
`loss(Ta + (α * G / K + 1)) > α * G` whenever `U ≥ 0` and `K > 0`. -/
lemma receiverLoss_gt_at_large {U K Ta α G : ℝ} (hU : 0 ≤ U) (hK : 0 < K)
    (hTa : 0 ≤ Ta) (hαG : 0 < α * G) :
    α * G < receiverLoss U K Ta (Ta + (α * G / K + 1)) := by
  set d : ℝ := α * G / K + 1 with hd
  have hKne : K ≠ 0 := ne_of_gt hK
  have hpos : 0 < α * G / K := div_pos hαG hK
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  have hd1 : 1 ≤ d := by rw [hd]; linarith
  have hsub : Ta + d - Ta = d := by ring
  have hrad : d ^ 4 ≤ (Ta + d) ^ 4 - Ta ^ 4 := by
    have h1 : 0 ≤ Ta ^ 2 * (Ta * d) := mul_nonneg (sq_nonneg Ta) (mul_nonneg hTa hd0)
    have h2 : 0 ≤ (Ta * d) ^ 2 := sq_nonneg (Ta * d)
    have h3 : 0 ≤ (Ta * d) * d ^ 2 := mul_nonneg (mul_nonneg hTa hd0) (sq_nonneg d)
    nlinarith [h1, h2, h3]
  have hd2 : d ≤ d ^ 2 := by
    have h : 0 ≤ d * (d - 1) := mul_nonneg hd0 (sub_nonneg.mpr hd1)
    nlinarith [h]
  have hd24 : d ^ 2 ≤ d ^ 4 := by
    have h : 0 ≤ d ^ 2 * ((d - 1) * (d + 1)) :=
      mul_nonneg (sq_nonneg d) (mul_nonneg (sub_nonneg.mpr hd1) (by linarith))
    nlinarith [h]
  have hd4 : d ≤ d ^ 4 := le_trans hd2 hd24
  have hK4 : K * d ^ 4 ≤ K * ((Ta + d) ^ 4 - Ta ^ 4) :=
    mul_le_mul_of_nonneg_left hrad (le_of_lt hK)
  have hKd4 : K * d ≤ K * d ^ 4 := mul_le_mul_of_nonneg_left hd4 (le_of_lt hK)
  have hdiv : K * (α * G / K) = α * G := by
    rw [mul_comm K (α * G / K)]
    exact div_mul_cancel₀ _ hKne
  have hKUp : α * G < K * d := by
    have hexpand : K * (α * G / K + 1) = α * G + K := by
      rw [mul_add, hdiv, mul_one]
    rw [hd, hexpand]
    linarith [hK]
  have hUd : 0 ≤ U * d := mul_nonneg hU hd0
  unfold receiverLoss
  rw [hsub]
  linarith [hK4, hKd4, hKUp, hUd]

/-- Stagnation temperature existence and uniqueness: for `Ta, G > 0`,
`α ∈ (0, 1]`, `U ≥ 0`, `K > 0`, there is a unique `Tstag > Ta` with
`loss(Tstag) = α * G`. -/
lemma receiver_stagnationTemperature {Ta G α U K : ℝ} (hTa : 0 < Ta)
    (hG : 0 < G) (hα0 : 0 < α) (hα1 : α ≤ 1) (hU : 0 ≤ U) (hK : 0 < K) :
    ∃! Tstag : ℝ, Ta < Tstag ∧ receiverLoss U K Ta Tstag = α * G := by
  have _ := hα1
  have hαG : 0 < α * G := mul_pos hα0 hG
  have hpos : 0 < α * G / K := div_pos hαG hK
  have hle : Ta ≤ Ta + (α * G / K + 1) := by linarith
  have hgt : α * G < receiverLoss U K Ta (Ta + (α * G / K + 1)) :=
    receiverLoss_gt_at_large hU hK hTa.le hαG
  have hcont : ContinuousOn (fun T => receiverLoss U K Ta T)
      (Set.Icc Ta (Ta + (α * G / K + 1))) := by
    have hfc : Continuous (fun T => receiverLoss U K Ta T) := by
      unfold receiverLoss
      continuity
    exact hfc.continuousOn
  have hmem : α * G ∈ (fun T => receiverLoss U K Ta T) ''
      Set.Ioo Ta (Ta + (α * G / K + 1)) := by
    have hsub := intermediate_value_Ioo hle hcont
    apply hsub
    constructor
    · show receiverLoss U K Ta Ta < α * G
      rw [receiverLoss_ambient]
      exact hαG
    · show α * G < receiverLoss U K Ta (Ta + (α * G / K + 1))
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
