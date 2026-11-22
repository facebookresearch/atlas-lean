/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Physlib.Units.ISQBridge
public import Physlib.Units.WithDim.Basic

/-!
# Electrical dimensions

Dimensions of current, voltage, resistance, capacitance, inductance and related quantities over
Physlib's charge-based `LTMCTDimensionBase`, with dimensionally correct circuit laws.

## i. Overview

Physlib's `LTMCTDimensionBase` takes length `L𝓭`, time `T𝓭`, mass `M𝓭`, charge `C𝓭` and
temperature `Θ𝓭` as its base dimensions. Over it, this module defines the electrical dimensions
with the commutative-group structure of `Dimension`: current `C T⁻¹`, voltage `M L² T⁻² C⁻¹`,
resistance `M L² T⁻¹ C⁻²`, capacitance `C² T² M⁻¹ L⁻²`, inductance `M L² C⁻²`, conductance (the
inverse of resistance), permittivity (capacitance per length), permeability (inductance per
length) and power `M L² T⁻³`, the energy dimension of Physlib's `DimEnergy` per time. Their
exponent tuples and the product identities hold by computation: voltage times current is power,
`R C` and `L / R` are times, `G R` is dimensionless, resistance times current is voltage and
current times time is charge.

Physlib's `Dimension.toISQHom` sends the charge generator `C𝓭` to the ISQ product of electric
current and time. Under it the current alias is the ISQ current base quantity, so charge is SI
current times time, and volt, ohm, farad and henry acquire their SI exponents
`kg m² s⁻³ A⁻¹`, `kg m² s⁻³ A⁻²`, `kg⁻¹ m⁻² s⁴ A²` and `kg m² s⁻² A⁻²`.

Under a change of units `LTMCTUnitChoices.dimScale` is a monoid homomorphism into the positive
reals, so a current coordinate rescales by the charge scale over the (positive) time scale and a
conductance coordinate by the inverse resistance scale. Ohm's law `V = R I`, `P = V I`, the time
constants `τ = R C` and `τ = L / R`, and `Q = I t`, stated on `WithDim` coordinates, are
dimensionally correct in Physlib's sense `IsDimensionallyCorrect`: they hold in every unit choice
or in none. The deliberately wrong laws `P = V + I` and `f = R C` (a time constant read as a
frequency) are not: each holds at concrete values in `SI` and fails after the change to Physlib's
`SIPrimed`.

Non-goals: no new dimension algebra or unit system is introduced, and no SI value of any
constant is asserted. `LRTimeConstant` uses Lean's `x / 0 = 0` when `R = 0`; the law is still
unit invariant because both sides rescale together. No circuit model is built.

## ii. Key results

- `currentDim_eq`, `voltageDim_eq`, `resistanceDim_eq`, `capacitanceDim_eq`, `inductanceDim_eq`,
  `conductanceDim_eq`, `permittivityDim_eq`, `permeabilityDim_eq`, `powerDim_eq` : the exponent
  tuples.
- `voltageDim_mul_currentDim`, `resistanceDim_mul_capacitanceDim`,
  `inductanceDim_div_resistanceDim`, `conductanceDim_mul_resistanceDim`,
  `resistanceDim_mul_currentDim`, `currentDim_mul_time` : the circuit identities.
- `toISQHom_currentDim`, `toISQHom_charge_eq_current_mul_time` and the SI exponent lemmas
  `toISQHom_voltageDim_exponent`, `toISQHom_resistanceDim_exponent`,
  `toISQHom_capacitanceDim_exponent`, `toISQHom_inductanceDim_exponent` : the ISQ bridge.
- `ohmLaw_isDimensionallyCorrect`, `powerLaw_isDimensionallyCorrect`,
  `rcTimeConstant_isDimensionallyCorrect`, `lrTimeConstant_isDimensionallyCorrect`,
  `chargeLaw_isDimensionallyCorrect` : the circuit laws are unit independent.
- `voltagePlusCurrent_not_isDimensionallyCorrect`, `rcAsFrequency_not_isDimensionallyCorrect` :
  two dimensionally wrong laws are rejected.
- `electricalDimensions_correct` : the main identities and the ISQ bridge together.

## iii. Table of contents

- A. Electrical dimension aliases over `LTMCTDimensionBase`
  - A.1. Exponent tuples
- B. Dimension identities
- C. The ISQ bridge: charge = SI current * time
- D. Coordinates under a change of units
- E. Unit-independent laws
- F. Headline result

## iv. References

- BIPM, *The International System of Units (SI)*, 9th edition (2019): coherent derived units
  volt, ohm, farad, henry and siemens and their expressions in base units.
- ISO 80000-6, *Quantities and units — Part 6: Electromagnetism*.
- `Physlib.Units.LTMCTDimensionBase`, `Physlib.Units.ISQBridge`, `Physlib.Units.Basic`,
  `Physlib.Units.UnitDependent` and `Physlib.Units.WithDim.Basic` in
  https://github.com/leanprover-community/physlib at the root package's pin; the
  `IsDimensionallyCorrect` proofs follow the pattern of `Physlib.Units.Examples`.
-/

@[expose] public section

open Dimension

namespace Units.ElectricalDimensions

/-! ## A. Electrical dimension aliases over `LTMCTDimensionBase` -/

/-- Electric current `C T⁻¹`. -/
def currentDim : Dimension LTMCTDimensionBase := C𝓭 * T𝓭⁻¹

/-- Voltage `M L² T⁻² C⁻¹`. -/
def voltageDim : Dimension LTMCTDimensionBase := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Resistance `M L² T⁻¹ C⁻²`. -/
def resistanceDim : Dimension LTMCTDimensionBase := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- Capacitance `C² T² M⁻¹ L⁻²`. -/
def capacitanceDim : Dimension LTMCTDimensionBase := C𝓭 * C𝓭 * T𝓭 * T𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- Inductance `M L² C⁻²`. -/
def inductanceDim : Dimension LTMCTDimensionBase := M𝓭 * L𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- Conductance, the inverse of resistance. -/
def conductanceDim : Dimension LTMCTDimensionBase := resistanceDim⁻¹

/-- Permittivity, capacitance per length. -/
def permittivityDim : Dimension LTMCTDimensionBase := capacitanceDim / L𝓭

/-- Permeability, inductance per length. -/
def permeabilityDim : Dimension LTMCTDimensionBase := inductanceDim / L𝓭

/-- Power `M L² T⁻³`: the energy dimension `M L² T⁻²` of Physlib's `DimEnergy` per time. -/
def powerDim : Dimension LTMCTDimensionBase := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-! ### A.1. Exponent tuples `⟨length, time, mass, charge, temperature⟩` -/

lemma currentDim_eq : currentDim = ofLTMCTDimensionBase 0 (-1) 0 1 0 := by
  rfl

lemma voltageDim_eq : voltageDim = ofLTMCTDimensionBase 2 (-2) 1 (-1) 0 := by
  rfl

lemma resistanceDim_eq : resistanceDim = ofLTMCTDimensionBase 2 (-1) 1 (-2) 0 := by
  rfl

lemma capacitanceDim_eq : capacitanceDim = ofLTMCTDimensionBase (-2) 2 (-1) 2 0 := by
  rfl

lemma inductanceDim_eq : inductanceDim = ofLTMCTDimensionBase 2 0 1 (-2) 0 := by
  rfl

lemma conductanceDim_eq : conductanceDim = ofLTMCTDimensionBase (-2) 1 (-1) 2 0 := by
  rfl

lemma permittivityDim_eq : permittivityDim = ofLTMCTDimensionBase (-3) 2 (-1) 2 0 := by
  rfl

lemma permeabilityDim_eq : permeabilityDim = ofLTMCTDimensionBase 1 0 1 (-2) 0 := by
  rfl

lemma powerDim_eq : powerDim = ofLTMCTDimensionBase 2 (-3) 1 0 0 := by
  rfl

/-! ## B. Dimension identities -/

/-- Power is energy per time (energy dimension as in Physlib's `DimEnergy`). -/
lemma powerDim_mul_time : powerDim * T𝓭 = M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ := by
  rfl

/-- Voltage times current has the power dimension. -/
lemma voltageDim_mul_currentDim : voltageDim * currentDim = powerDim := by
  rfl

/-- Resistance times capacitance has the time dimension. -/
lemma resistanceDim_mul_capacitanceDim : resistanceDim * capacitanceDim = T𝓭 := by
  rfl

/-- Inductance over resistance has the time dimension. -/
lemma inductanceDim_div_resistanceDim : inductanceDim / resistanceDim = T𝓭 := by
  rfl

/-- Conductance times resistance is dimensionless. -/
lemma conductanceDim_mul_resistanceDim : conductanceDim * resistanceDim = 1 := by
  rfl

/-- Ohm's law at the level of dimensions: resistance times current is a voltage. -/
lemma resistanceDim_mul_currentDim : resistanceDim * currentDim = voltageDim := by
  rfl

/-- Current times time is charge. -/
lemma currentDim_mul_time : currentDim * T𝓭 = C𝓭 := by
  rfl

/-- Permittivity times length is capacitance. -/
lemma permittivityDim_mul_length : permittivityDim * L𝓭 = capacitanceDim := by
  rfl

/-- Permeability times length is inductance. -/
lemma permeabilityDim_mul_length : permeabilityDim * L𝓭 = inductanceDim := by
  rfl

/-- Permittivity times permeability is an inverse squared speed `T² L⁻²`. -/
lemma permittivityDim_mul_permeabilityDim :
    permittivityDim * permeabilityDim = T𝓭 * T𝓭 * L𝓭⁻¹ * L𝓭⁻¹ := by
  rfl

/-- R C is not an inverse time (a frequency). -/
lemma resistanceDim_mul_capacitanceDim_ne_inv_time : resistanceDim * capacitanceDim ≠ T𝓭⁻¹ := by
  decide

/-- Voltage and current have different dimensions, so `V + I` has no dimension. -/
lemma voltageDim_ne_currentDim : voltageDim ≠ currentDim := by
  decide

/-! ## C. The ISQ bridge: charge = SI current * time -/

/-- `toISQHom` sends PhysLib's time generator to the ISQ time base. -/
lemma toISQHom_time : toISQHom T𝓭 = single ISQDimensionBase.time := by
  ext b
  cases b <;> simp [toISQHom_apply, toISQFun, T𝓭, single_exponent]

/-- `toISQHom` sends the current alias to the ISQ electric-current base quantity. -/
lemma toISQHom_currentDim : toISQHom currentDim = single ISQDimensionBase.current := by
  ext b
  cases b <;> simp [toISQHom_apply, toISQFun, currentDim, C𝓭, T𝓭, single_exponent]

/-- Charge is SI current times time under `toISQHom`. -/
lemma toISQHom_charge_eq_current_mul_time :
    toISQHom C𝓭 = toISQHom currentDim * toISQHom T𝓭 := by
  rw [← map_mul]
  rfl

/-- The same statement in ISQ base quantities: `toISQHom C𝓭 = I · T`. -/
lemma toISQHom_charge_eq_single_current_mul_single_time :
    toISQHom C𝓭 = single ISQDimensionBase.current * single ISQDimensionBase.time := by
  exact toISQHom_C𝓭

/-- The SI exponents of voltage: `kg m² s⁻³ A⁻¹`. -/
lemma toISQHom_voltageDim_exponent (b : ISQDimensionBase) :
    (toISQHom voltageDim).exponent b =
      match b with
      | .length => 2
      | .mass => 1
      | .time => -3
      | .current => -1
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> rfl

/-- The SI exponents of resistance: `kg m² s⁻³ A⁻²`. -/
lemma toISQHom_resistanceDim_exponent (b : ISQDimensionBase) :
    (toISQHom resistanceDim).exponent b =
      match b with
      | .length => 2
      | .mass => 1
      | .time => -3
      | .current => -2
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> rfl

/-- The SI exponents of capacitance: `kg⁻¹ m⁻² s⁴ A²`. -/
lemma toISQHom_capacitanceDim_exponent (b : ISQDimensionBase) :
    (toISQHom capacitanceDim).exponent b =
      match b with
      | .length => -2
      | .mass => -1
      | .time => 4
      | .current => 2
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> rfl

/-- The SI exponents of inductance: `kg m² s⁻² A⁻²`. -/
lemma toISQHom_inductanceDim_exponent (b : ISQDimensionBase) :
    (toISQHom inductanceDim).exponent b =
      match b with
      | .length => 2
      | .mass => 1
      | .time => -2
      | .current => -2
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> rfl

/-! ## D. Coordinates under a change of units -/

/-- A current coordinate rescales by the charge scale over the time scale; the time scale in
the denominator is positive (`LTMCTUnitChoices.dimScale_pos`). -/
lemma dimScale_currentDim (u1 u2 : LTMCTUnitChoices) :
    (u1.dimScale u2 currentDim : ℝ) = (u1.dimScale u2 C𝓭 : ℝ) / (u1.dimScale u2 T𝓭 : ℝ) := by
  simp [currentDim, map_mul, map_inv, div_eq_mul_inv]

/-- A conductance coordinate rescales by the inverse of the resistance scale. -/
lemma dimScale_conductanceDim (u1 u2 : LTMCTUnitChoices) :
    (u1.dimScale u2 conductanceDim : ℝ) = (u1.dimScale u2 resistanceDim : ℝ)⁻¹ := by
  simp [conductanceDim, map_inv]

/-- The charge `Q = I t` of a current over a time, typed by `WithDim`. -/
def chargeOfCurrent (I : WithDim currentDim ℝ) (t : WithDim T𝓭 ℝ) : WithDim C𝓭 ℝ :=
  WithDim.cast (I * t) (by rfl)

/-- The coordinate of `chargeOfCurrent I t` is `I t`. -/
lemma chargeOfCurrent_val (I : WithDim currentDim ℝ) (t : WithDim T𝓭 ℝ) :
    (chargeOfCurrent I t).val = I.val * t.val := by
  rfl

/-! ## E. Unit-independent laws -/

/-- Ohm's law `V = R I`. -/
def OhmLaw (V : WithDim voltageDim ℝ) (R : WithDim resistanceDim ℝ)
    (I : WithDim currentDim ℝ) : Prop :=
  V.val = R.val * I.val

/-- Electrical power `P = V I`. -/
def PowerLaw (P : WithDim powerDim ℝ) (V : WithDim voltageDim ℝ)
    (I : WithDim currentDim ℝ) : Prop :=
  P.val = V.val * I.val

/-- The RC time constant `τ = R C`. -/
def RCTimeConstant (τ : WithDim T𝓭 ℝ) (R : WithDim resistanceDim ℝ)
    (C : WithDim capacitanceDim ℝ) : Prop :=
  τ.val = R.val * C.val

/-- The L/R time constant `τ = L / R`. -/
def LRTimeConstant (τ : WithDim T𝓭 ℝ) (L : WithDim inductanceDim ℝ)
    (R : WithDim resistanceDim ℝ) : Prop :=
  τ.val = L.val / R.val

/-- Charge accumulated by a constant current, `Q = I t`. -/
def ChargeLaw (Q : WithDim C𝓭 ℝ) (I : WithDim currentDim ℝ) (t : WithDim T𝓭 ℝ) : Prop :=
  Q.val = I.val * t.val

/-- A deliberately wrong law: power read as voltage plus current. -/
def VoltagePlusCurrent (P : WithDim powerDim ℝ) (V : WithDim voltageDim ℝ)
    (I : WithDim currentDim ℝ) : Prop :=
  P.val = V.val + I.val

/-- A deliberately wrong law: R C read as a frequency. -/
def RCAsFrequency (f : WithDim T𝓭⁻¹ ℝ) (R : WithDim resistanceDim ℝ)
    (C : WithDim capacitanceDim ℝ) : Prop :=
  f.val = R.val * C.val

/-- Ohm's law `V = R I` is unchanged by every change of units. -/
theorem ohmLaw_isDimensionallyCorrect : IsDimensionallyCorrect OhmLaw := by
  simp only [isDimensionallyCorrect_fun_iff, funext_iff, UnitDependent.scaleUnit_apply_fun,
    UnitDependent.scaleUnit_apply_fun_left, OhmLaw,
    WithDim.val_mul_eq_mul, DMul.hMul_scaleUnit, eq_iff_iff]
  intros
  rw [WithDim.scaleUnit_val_eq_scaleUnit_val_of_dim_eq (by rfl)]

/-- The power law `P = V I` is unchanged by every change of units. -/
theorem powerLaw_isDimensionallyCorrect : IsDimensionallyCorrect PowerLaw := by
  simp only [isDimensionallyCorrect_fun_iff, funext_iff, UnitDependent.scaleUnit_apply_fun,
    UnitDependent.scaleUnit_apply_fun_left, PowerLaw,
    WithDim.val_mul_eq_mul, DMul.hMul_scaleUnit, eq_iff_iff]
  intros
  rw [WithDim.scaleUnit_val_eq_scaleUnit_val_of_dim_eq (by rfl)]

/-- The RC time constant `τ = R C` is unchanged by every change of units. -/
theorem rcTimeConstant_isDimensionallyCorrect : IsDimensionallyCorrect RCTimeConstant := by
  simp only [isDimensionallyCorrect_fun_iff, funext_iff, UnitDependent.scaleUnit_apply_fun,
    UnitDependent.scaleUnit_apply_fun_left, RCTimeConstant,
    WithDim.val_mul_eq_mul, DMul.hMul_scaleUnit, eq_iff_iff]
  intros
  rw [WithDim.scaleUnit_val_eq_scaleUnit_val_of_dim_eq (by rfl)]

/-- The L/R time constant `τ = L / R` is unchanged by every change of units. -/
theorem lrTimeConstant_isDimensionallyCorrect : IsDimensionallyCorrect LRTimeConstant := by
  simp only [isDimensionallyCorrect_fun_iff, funext_iff, UnitDependent.scaleUnit_apply_fun,
    UnitDependent.scaleUnit_apply_fun_left, LRTimeConstant,
    WithDim.val_div_val, WithDim.div_scaleUnit, eq_iff_iff]
  intros
  rw [WithDim.scaleUnit_val_eq_scaleUnit_val_of_dim_eq (by rfl)]

/-- The charge law `Q = I t` is unchanged by every change of units. -/
theorem chargeLaw_isDimensionallyCorrect : IsDimensionallyCorrect ChargeLaw := by
  simp only [isDimensionallyCorrect_fun_iff, funext_iff, UnitDependent.scaleUnit_apply_fun,
    UnitDependent.scaleUnit_apply_fun_left, ChargeLaw,
    WithDim.val_mul_eq_mul, DMul.hMul_scaleUnit, eq_iff_iff]
  intros
  rw [WithDim.scaleUnit_val_eq_scaleUnit_val_of_dim_eq (by rfl)]

/-- `P = V + I` is not dimensionally correct: it holds at `P = 2`, `V = 1`, `I = 1` in SI units
but fails after the change to `SIPrimed`. -/
lemma voltagePlusCurrent_not_isDimensionallyCorrect :
    ¬ IsDimensionallyCorrect VoltagePlusCurrent := by
  simp only [isDimensionallyCorrect_fun_iff, not_forall, funext_iff,
    UnitDependent.scaleUnit_apply_fun]
  use LTMCTUnitChoices.SI, LTMCTUnitChoices.SIPrimed, ⟨2⟩, ⟨1⟩, ⟨1⟩
  unfold VoltagePlusCurrent
  simp only [WithDim.scaleUnit_val, powerDim_eq, voltageDim_eq,
    LTMCTUnitChoices.dimScale_SIPrimed_SI]
  simp only [UnitDependent.scaleUnit_apply_fun_left, WithDim.scaleUnit_val, currentDim_eq,
    LTMCTUnitChoices.dimScale_SIPrimed_SI]
  norm_num [NNReal.smul_def]

/-- `f = R C` with `f` a frequency is not dimensionally correct: it holds at `f = 6`, `R = 2`,
`C = 3` in SI units but fails after the change to `SIPrimed`. -/
lemma rcAsFrequency_not_isDimensionallyCorrect : ¬ IsDimensionallyCorrect RCAsFrequency := by
  simp only [isDimensionallyCorrect_fun_iff, not_forall, funext_iff,
    UnitDependent.scaleUnit_apply_fun]
  use LTMCTUnitChoices.SI, LTMCTUnitChoices.SIPrimed, ⟨6⟩, ⟨2⟩, ⟨3⟩
  unfold RCAsFrequency
  have hT : (T𝓭⁻¹ : Dimension LTMCTDimensionBase) = ofLTMCTDimensionBase 0 (-1) 0 0 0 := rfl
  simp only [WithDim.scaleUnit_val, hT, resistanceDim_eq,
    LTMCTUnitChoices.dimScale_SIPrimed_SI]
  simp only [UnitDependent.scaleUnit_apply_fun_left, WithDim.scaleUnit_val, capacitanceDim_eq,
    LTMCTUnitChoices.dimScale_SIPrimed_SI]
  norm_num [NNReal.smul_def]

/-! ## F. Headline result -/

/-- The electrical aliases over `LTMCTDimensionBase` satisfy the power, time-constant,
conductance and permittivity/permeability identities, and `toISQHom` reads current as the ISQ
current base and charge as current times time. -/
lemma electricalDimensions_correct :
    voltageDim * currentDim = powerDim ∧
    resistanceDim * capacitanceDim = T𝓭 ∧
    inductanceDim / resistanceDim = T𝓭 ∧
    conductanceDim * resistanceDim = 1 ∧
    permittivityDim = ofLTMCTDimensionBase (-3) 2 (-1) 2 0 ∧
    permeabilityDim = ofLTMCTDimensionBase 1 0 1 (-2) 0 ∧
    toISQHom currentDim = single ISQDimensionBase.current ∧
    toISQHom C𝓭 = toISQHom currentDim * toISQHom T𝓭 := by
  exact ⟨voltageDim_mul_currentDim, resistanceDim_mul_capacitanceDim,
    inductanceDim_div_resistanceDim, conductanceDim_mul_resistanceDim, permittivityDim_eq,
    permeabilityDim_eq, toISQHom_currentDim, toISQHom_charge_eq_current_mul_time⟩

end Units.ElectricalDimensions
