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
public import PhyslibExt.FluidDynamics.RotorPorts
public import PhyslibExt.SpaceSystems.MissionLedger

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Renewable energy ports: solar-thermal receiver balance and wind power curve

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

Section B treats a wind turbine described by a supplied power curve of the hub-height wind speed
`U ≥ 0`, a speed magnitude. The cut-in, rated and cut-out speeds are supplied nominal regime
thresholds with `0 ≤ U_ci < U_r < U_co`, the rated power is `P_r > 0`, and the operating curve on
the partial-load regime is a model or calibration input with no assumed shape or sign. The
thresholds assign each speed to one regime of the piecewise curve: zero below cut-in (`U < U_ci`);
the supplied curve on the partial-load regime `U_ci ≤ U < U_r`, cut-in included; the rated power on
the rated regime `U_r ≤ U ≤ U_co`, both ends included; zero above cut-out (`U_co < U`). At every
`U ≥ 0` each produced value is clipped between zero and `min P_r (betzPower ρ A U)`, where
`betzPower ρ A U = (16/27) ρ A U³ / 2` is the Betz limit times the freestream kinetic power through
the swept area `A ≥ 0` at the air density `ρ ≥ 0`. The thresholds carry no attainment meaning: the
rated speed need not be the lowest speed at which the power reaches `P_r`, a regime may evaluate to
zero, and `ρ = 0` or `A = 0` makes the Betz cap zero.

The Betz limit is not derived again. It is the bound
`FluidDynamics.RotorPorts.powerCoefficient_le_betz` of the ideal actuator disk on the
wind-extraction branch `0 < U_w < U∞`, with positive density and area: such a disk extracts at most
`betzPower ρ A U∞`, exactly that power at the induction factor `1/3`. The bound is used only under
those assumptions; the supplied curve itself is a model input, not a consequence of the disk.

A wind record of `N` intervals gives interval `k` the speed `U k` and the duration `dt k ≥ 0`. The
energy delivered by the first `t` intervals is the mission-ledger stock
(`PhyslibExt.SpaceSystems.MissionLedger`), from zero, of the interval energies `P(U k) dt k`, and
the elapsed time is `T_t = ∑_{k < t} dt k`. At every prefix `t ≤ N`, start and end included,
`0 ≤ E_t ≤ P_r T_t`; with `T_N > 0` the capacity factor `E_N / (P_r T_N)` lies in `[0, 1]`. Peaks
of different turbines are not assumed simultaneous: the sum of their individual maxima can exceed
the largest simultaneous sum.

Model inputs of section B: the supplied curve and its regime thresholds, one speed per interval of
the wind record, and the ideal-disk assumptions of the reused Betz bound. No turbulence,
availability, wake-loss or grid model is used, and no empirical adequacy or turbine safety claim is
made.

## ii. Key results

- `RenewableEnergyPorts.receiver_stagnationTemperature`: for
  `Ta, G > 0`, `α ∈ (0, 1]`, `U ≥ 0`, `K > 0` there is a unique
  `Tstag > Ta` with `receiverLoss U K Ta Tstag = α * G`.
- `RenewableEnergyPorts.receiverLoss_strictMonoOn`: the loss is
  strictly increasing on `[Ta, ∞)` for `Ta ≥ 0`.
- `RenewableEnergyPorts.WindPowerCurve.power`: the range-guarded, clipped power curve, with
  `power_eq_zero_of_lt_cutIn`, `power_eq_of_partialLoad`, `power_eq_of_rated` and
  `power_eq_zero_of_cutOut_lt` for its four regimes.
- `RenewableEnergyPorts.WindPowerCurve.power_nonneg_le`: `0 ≤ P(U) ≤ min P_r (betzPower ρ A U)`
  on `U ≥ 0`.
- `RenewableEnergyPorts.extractedPower_le_betzPower`: the Betz cap is the actuator-disk limit.
- `RenewableEnergyPorts.windEnergy_nonneg_le`, `RenewableEnergyPorts.capacityFactor_nonneg_le_one`:
  `0 ≤ E_t ≤ P_r T_t` at every prefix and `0 ≤ CF ≤ 1`.
- Operating and shutdown intervals, peaks that are not simultaneous, and an active Betz clip with
  the cut-out endpoint are checked on an example `2 MW` curve in
  `PhyslibExtTest.Thermodynamics.RenewableEnergyPortsTest`.

## iii. Table of contents

- A. Receiver loss and stagnation temperature
- B. Wind power curve and finite-time energy

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
- IEC 61400-1, *Wind energy generation systems, Part 1: Design requirements*: the terms cut-in,
  rated and cut-out wind speed. Section B uses them only to name supplied regime thresholds; the
  standard's attainment meanings are not properties of `WindPowerCurve`.
- IEC 61400-12-1, *Wind energy generation systems, Part 12-1: Power performance measurements of
  electricity producing wind turbines*: the measured power curve, a calibration input.
- J. F. Manwell, J. G. McGowan and A. L. Rogers, *Wind Energy Explained*, Wiley, ch. 2 (power
  curves, energy production over a period and the capacity factor) and ch. 3 (the Betz limit).
- `PhyslibExt.FluidDynamics.RotorPorts`: the ideal actuator disk and the Betz limit, reused;
  `PhyslibExt.SpaceSystems.MissionLedger`: the prefix stock of a finite schedule, reused.

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

/-! ## B. Wind power curve and finite-time energy -/

/-- The Betz power `(16/27) ρ A U³ / 2`: the Betz limit `16/27` of
`FluidDynamics.RotorPorts.powerCoefficient_le_betz` times the freestream kinetic power
`FluidDynamics.RotorPorts.powerNormalization ρ A U` through the swept area `A`. -/
noncomputable def betzPower (ρ A U : ℝ) : ℝ :=
  16 / 27 * FluidDynamics.RotorPorts.powerNormalization ρ A U

/-- A supplied wind-turbine power curve. The cut-in, rated and cut-out speeds are nominal regime
thresholds with `0 ≤ U_ci < U_r < U_co`, the rated power is positive, and the air density and the
swept area of the Betz cap are nonnegative. The operating curve is the supplied partial-load curve,
a model or calibration input with no assumed shape or sign, evaluated only on `U_ci ≤ U < U_r`.
The thresholds select the regimes of `power` and carry no attainment meaning: the rated speed need
not be the lowest speed at which the power reaches the rated power, a regime may evaluate to zero,
and `ρ = 0` or `A = 0` makes the Betz cap zero. -/
structure WindPowerCurve where
  /-- The cut-in threshold `U_ci`, the lower end of the partial-load regime. -/
  uCutIn : ℝ
  /-- The rated threshold `U_r`, the lower end of the rated regime. -/
  uRated : ℝ
  /-- The cut-out threshold `U_co`, the upper end of the rated regime. -/
  uCutOut : ℝ
  /-- The rated power `P_r`. -/
  pRated : ℝ
  /-- The air density `ρ`. -/
  ρ : ℝ
  /-- The swept area `A` of the rotor. -/
  A : ℝ
  /-- The supplied partial-load operating curve. -/
  operating : ℝ → ℝ
  /-- The cut-in threshold is nonnegative. -/
  cutIn_nonneg : 0 ≤ uCutIn
  /-- The cut-in threshold is below the rated threshold. -/
  cutIn_lt_rated : uCutIn < uRated
  /-- The rated threshold is below the cut-out threshold. -/
  rated_lt_cutOut : uRated < uCutOut
  /-- The rated power is positive. -/
  pRated_pos : 0 < pRated
  /-- The density is nonnegative. -/
  ρ_nonneg : 0 ≤ ρ
  /-- The swept area is nonnegative. -/
  A_nonneg : 0 ≤ A

namespace WindPowerCurve

/-- The clip of a value `x` at the wind speed `U`, `max 0 (min x (min P_r (betzPower ρ A U)))`.
For `U ≥ 0` the cap `min P_r (betzPower ρ A U)` is nonnegative (`ρ, A ≥ 0`) and the clip lies
between zero and the cap; for `U < 0` the clip is zero. -/
noncomputable def clip (c : WindPowerCurve) (U x : ℝ) : ℝ :=
  max 0 (min x (min c.pRated (betzPower c.ρ c.A U)))

/-- The evaluated power at the wind speed `U`: zero below cut-in, the clipped supplied curve on the
partial-load regime `U_ci ≤ U < U_r`, the clipped rated power on the rated regime
`U_r ≤ U ≤ U_co`, and zero above cut-out. The thresholds assign `U_ci` to the partial-load regime
and `U_r`, `U_co` to the rated regime; a regime may still evaluate to zero. -/
noncomputable def power (c : WindPowerCurve) (U : ℝ) : ℝ :=
  if U < c.uCutIn then 0
  else if U < c.uRated then c.clip U (c.operating U)
  else if U ≤ c.uCutOut then c.clip U c.pRated
  else 0

/-- **Below cut-in** the turbine is parked: `P(U) = 0` for `U < U_ci`. -/
lemma power_eq_zero_of_lt_cutIn (c : WindPowerCurve) {U : ℝ} (hU : U < c.uCutIn) :
    c.power U = 0 := by
  unfold power
  rw [ite_eq_left hU]

/-- **Partial load.** On `U_ci ≤ U < U_r`, cut-in included, the power is the supplied curve clipped
between zero and `min P_r (betzPower ρ A U)`. -/
lemma power_eq_of_partialLoad (c : WindPowerCurve) {U : ℝ}
    (hU : U ∈ Set.Ico c.uCutIn c.uRated) : c.power U = c.clip U (c.operating U) := by
  obtain ⟨hlo, hhi⟩ := hU
  unfold power
  rw [ite_eq_right (not_lt.mpr hlo), ite_eq_left hhi]

/-- **Rated regime.** On `U_r ≤ U ≤ U_co`, both endpoints included, the power is
`min P_r (betzPower ρ A U)`; it is the rated power when the Betz power at the rated speed covers the
rated power. -/
lemma power_eq_of_rated (c : WindPowerCurve) {U : ℝ} (hU : U ∈ Set.Icc c.uRated c.uCutOut) :
    c.power U = min c.pRated (betzPower c.ρ c.A U) ∧
      (c.pRated ≤ betzPower c.ρ c.A c.uRated → c.power U = c.pRated) := by
  obtain ⟨hlo, hhi⟩ := hU
  have hlt1 : ¬ U < c.uCutIn := not_lt.mpr (le_trans c.cutIn_lt_rated.le hlo)
  have hlt2 : ¬ U < c.uRated := not_lt.mpr hlo
  have hpow : c.power U = c.clip U c.pRated := by
    unfold power
    rw [ite_eq_right hlt1, ite_eq_right hlt2, ite_eq_left hhi]
  have hU0 : 0 ≤ U := le_trans (le_trans c.cutIn_nonneg c.cutIn_lt_rated.le) hlo
  have hbz : 0 ≤ betzPower c.ρ c.A U := by
    unfold betzPower FluidDynamics.RotorPorts.powerNormalization
    have hρ := c.ρ_nonneg
    have hA := c.A_nonneg
    positivity
  have hmin : min c.pRated (min c.pRated (betzPower c.ρ c.A U)) =
      min c.pRated (betzPower c.ρ c.A U) := by
    rw [← min_assoc, min_eq_left le_rfl]
  have hmain : c.power U = min c.pRated (betzPower c.ρ c.A U) := by
    rw [hpow]
    unfold clip
    rw [hmin, max_eq_right (le_min c.pRated_pos.le hbz)]
  refine ⟨hmain, fun hle => ?_⟩
  rw [hmain]
  have hmono : c.uRated ^ 3 ≤ U ^ 3 :=
    pow_le_pow_left₀ (le_trans c.cutIn_nonneg c.cutIn_lt_rated.le) hlo 3
  have hleU : c.pRated ≤ betzPower c.ρ c.A U := by
    have hρA : 0 ≤ c.ρ * c.A := mul_nonneg c.ρ_nonneg c.A_nonneg
    have h := mul_nonneg hρA (sub_nonneg.mpr hmono)
    unfold betzPower FluidDynamics.RotorPorts.powerNormalization at hle ⊢
    linarith
  exact min_eq_left hleU

/-- **Above cut-out** the turbine is shut down: `P(U) = 0` for `U_co < U`. -/
lemma power_eq_zero_of_cutOut_lt (c : WindPowerCurve) {U : ℝ} (hU : c.uCutOut < U) :
    c.power U = 0 := by
  have hlt1 : ¬ U < c.uCutIn :=
    not_lt.mpr (le_trans c.cutIn_lt_rated.le (le_trans c.rated_lt_cutOut.le hU.le))
  have hlt2 : ¬ U < c.uRated := not_lt.mpr (le_trans c.rated_lt_cutOut.le hU.le)
  have hle : ¬ U ≤ c.uCutOut := not_le.mpr hU
  unfold power
  rw [ite_eq_right hlt1, ite_eq_right hlt2, ite_eq_right hle]

/-- **The clip.** At every wind speed the power is nonnegative and at most the rated power, and at
every `U ≥ 0` it is at most the Betz power: `0 ≤ P(U) ≤ min P_r (betzPower ρ A U)` on `U ≥ 0`.
Speeds below the nonnegative cut-in speed give zero. -/
lemma power_nonneg_le (c : WindPowerCurve) (U : ℝ) :
    0 ≤ c.power U ∧ c.power U ≤ c.pRated ∧ (0 ≤ U → c.power U ≤ betzPower c.ρ c.A U) := by
  have hbz : 0 ≤ U → 0 ≤ betzPower c.ρ c.A U := by
    intro hU
    unfold betzPower FluidDynamics.RotorPorts.powerNormalization
    have hρ := c.ρ_nonneg
    have hA := c.A_nonneg
    positivity
  have hclip : ∀ x : ℝ, 0 ≤ c.clip U x ∧ c.clip U x ≤ c.pRated ∧
      (0 ≤ U → c.clip U x ≤ betzPower c.ρ c.A U) := by
    intro x
    unfold clip
    refine ⟨le_max_left _ _, max_le c.pRated_pos.le
      ((min_le_right _ _).trans (min_le_left _ _)), ?_⟩
    intro hU
    exact max_le (hbz hU) ((min_le_right _ _).trans (min_le_right _ _))
  by_cases h1 : U < c.uCutIn
  · rw [c.power_eq_zero_of_lt_cutIn h1]
    exact ⟨le_rfl, c.pRated_pos.le, hbz⟩
  · have h1' : c.uCutIn ≤ U := not_lt.mp h1
    by_cases h2 : U < c.uRated
    · rw [c.power_eq_of_partialLoad ⟨h1', h2⟩]
      exact hclip _
    · have h2' : c.uRated ≤ U := not_lt.mp h2
      by_cases h3 : U ≤ c.uCutOut
      · have hU0 : 0 ≤ U := le_trans (le_trans c.cutIn_nonneg c.cutIn_lt_rated.le) h2'
        rw [(c.power_eq_of_rated ⟨h2', h3⟩).1]
        exact ⟨le_min c.pRated_pos.le (hbz hU0), min_le_left _ _, fun _ => min_le_right _ _⟩
      · have h3' : c.uCutOut < U := lt_of_not_ge h3
        rw [c.power_eq_zero_of_cutOut_lt h3']
        exact ⟨le_rfl, c.pRated_pos.le, hbz⟩

end WindPowerCurve

/-- **The Betz cap is the actuator-disk limit.** On the wind-extraction branch `0 < U_w < U∞`, with
positive density and area, an ideal actuator disk extracts at most the Betz power of its density,
area and freestream speed, with equality exactly at the induction factor `1/3`: the bound
`FluidDynamics.RotorPorts.powerCoefficient_le_betz` in power units. -/
lemma extractedPower_le_betzPower {d : FluidDynamics.RotorPorts.ActuatorDisk} (h : d.PortLaws)
    (hρ : 0 < d.ρ) (hA : 0 < d.A) (hw : 0 < d.uWake) (hext : d.uWake < d.uInf) :
    FluidDynamics.RotorPorts.extractedPower d ≤ betzPower d.ρ d.A d.uInf ∧
      (FluidDynamics.RotorPorts.extractedPower d = betzPower d.ρ d.A d.uInf ↔
        FluidDynamics.RotorPorts.inductionFactor d = 1 / 3) := by
  obtain ⟨-, -, hle, hiff⟩ :=
    FluidDynamics.RotorPorts.powerCoefficient_le_betz h hρ hA hw hext
  have hU : 0 < d.uInf := hw.trans hext
  have hN : 0 < FluidDynamics.RotorPorts.powerNormalization d.ρ d.A d.uInf := by
    unfold FluidDynamics.RotorPorts.powerNormalization
    positivity
  unfold FluidDynamics.RotorPorts.powerCoefficient at hle hiff
  unfold betzPower
  refine ⟨(div_le_iff₀ hN).mp hle, ?_⟩
  rw [← div_eq_iff hN.ne']
  exact hiff

/-- The elapsed time `T_t = ∑_{k < t} dt k` of the first `t` intervals. -/
def elapsedTime (dt : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range t, dt k

/-- The energy delivered by the first `t` intervals of a wind record, interval `k` at the speed
`U k` for the duration `dt k`: the mission-ledger stock, from zero, of the interval energies
`P(U k) dt k`. -/
noncomputable def windEnergy (c : WindPowerCurve) (U dt : ℕ → ℝ) (t : ℕ) : ℝ :=
  MissionLedger.stock (fun _ : Unit => 0) (fun _ k => c.power (U k) * dt k) () t

/-- The capacity factor of the first `N` intervals: the delivered energy over the energy
`P_r T_N` at rated power for the elapsed time, meaningful for `T_N > 0` only. -/
noncomputable def capacityFactor (c : WindPowerCurve) (U dt : ℕ → ℝ) (N : ℕ) : ℝ :=
  windEnergy c U dt N / (c.pRated * elapsedTime dt N)

/-- **Finite-time energy, checked at every prefix.** With nonnegative durations on the `N`
intervals, at every prefix `t ≤ N`, the start and the end included, the delivered energy is
nonnegative and at most the rated power times the elapsed time; at `t = N`, `E ≤ P_r T`. -/
lemma windEnergy_nonneg_le (c : WindPowerCurve) (U : ℕ → ℝ) {dt : ℕ → ℝ} {N : ℕ}
    (hdt : ∀ k < N, 0 ≤ dt k) {t : ℕ} (ht : t ≤ N) :
    0 ≤ windEnergy c U dt t ∧ windEnergy c U dt t ≤ c.pRated * elapsedTime dt t := by
  simp only [windEnergy, MissionLedger.stock, elapsedTime, zero_add, Finset.mul_sum]
  constructor
  · apply Finset.sum_nonneg
    intro k hk
    rw [Finset.mem_range] at hk
    exact mul_nonneg (c.power_nonneg_le _).1 (hdt k (lt_of_lt_of_le hk ht))
  · apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_range] at hk
    exact mul_le_mul_of_nonneg_right (c.power_nonneg_le _).2.1
      (hdt k (lt_of_lt_of_le hk ht))

/-- **Capacity factor.** With nonnegative durations and a positive elapsed time, the capacity
factor lies in `[0, 1]`. -/
lemma capacityFactor_nonneg_le_one (c : WindPowerCurve) (U : ℕ → ℝ) {dt : ℕ → ℝ} {N : ℕ}
    (hdt : ∀ k < N, 0 ≤ dt k) (hT : 0 < elapsedTime dt N) :
    0 ≤ capacityFactor c U dt N ∧ capacityFactor c U dt N ≤ 1 := by
  obtain ⟨hE0, hET⟩ := windEnergy_nonneg_le c U hdt (le_rfl : N ≤ N)
  have hD : 0 < c.pRated * elapsedTime dt N := mul_pos c.pRated_pos hT
  unfold capacityFactor
  constructor
  · exact div_nonneg hE0 hD.le
  · rw [div_le_one hD]
    exact hET

end RenewableEnergyPorts
