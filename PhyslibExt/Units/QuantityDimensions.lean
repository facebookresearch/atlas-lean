/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Physlib.Units.ISQBridge
public import Physlib.Units.ParametricUnits
public import Physlib.Units.WithDim.Basic

/-!
# Quantity dimensions, amount of substance, and constants

ISQ dimensions of amount-based quantities, unit-conversion round trips, the count–amount bridge
`n = N / N_A` with `R = N_A k_B`, and the dimensionless temperature, log and exp gates.

## i. Overview

In the International System of Quantities, amount of substance is an independent base quantity,
not a pure count. Over Physlib's seven-element basis `ISQDimensionBase`, this module defines the
dimensions of amount, amount concentration, molar mass, molar energy (also the dimension of molar
chemical potential), diffusivity, stress, energy, thermodynamic temperature and the molar gas
constant with `Dimension.single` and the commutative-group structure of `Dimension`. It computes
their exponents at all seven base quantities and their products. Amount is not dimensionless, and
the amount, length, mass, time and temperature dimensions are pairwise distinct.

A coordinate `x` of a quantity of dimension `d` in the unit choice `u1 : UnitScale B` has the
coordinate `u1.dimScale u2 d * x` in the unit choice `u2`, where `UnitScale.dimScale` is Physlib's
basis-generic scaling factor; the factor is positive by `UnitScale.scale_pos`. Converting and
converting back is the identity, the ratio of two coordinates of one dimension is unchanged, and a
dimensionless coordinate does not rescale. Physlib's projection `Dimension.fromISQHom` onto
`LTMCTDimensionBase` sends `amountDim` to `1` and is not injective. It must never be used as a
reversible conversion, and no conversion in this module is built on it.

The Avogadro constant `N_A` and the Boltzmann constant `k_B` are positive real parameters, and no
SI value is asserted for them. A particle count `N` is a dimensionless real, while the amount
`amountOfCount N_A N = N / N_A` carries the amount dimension: it lies in
`WithDim amountDim ℝ`. The molar gas constant is `R = N_A k_B`, and the molar energy of a
per-particle energy `e` is `E = N_A e`. This bridge is a definition together with its proved round
trips, not a proof that nature obeys it.

Absolute temperatures are positive reals: the inverse temperature `1 / (k_B T)` is positive for
`T > 0`, and the case `T = 0` is excluded by hypothesis. Celsius readings are affine reals
converted by `celsiusToKelvin`: Celsius and Kelvin differences agree, but Celsius readings do not
scale like absolute temperatures. `Real.log` and `Real.exp` are applied only to dimensionless real
arguments. `logRatio x x0` is the logarithm of the ratio of two positive coordinates of one
dimension, and `expScaledEnergy E R T` is `exp (-(E / (R T)))`, whose exponent has dimension
`molarEnergyDim / (gasConstantDim * temperatureDim) = 1`. Both are unchanged by a change of units.

Non-goals: this is not a full SI unit system, and Celsius readings are not given a `Temperature`
type. No claim is made that `Real.log` or `Real.exp` of a dimensional value is defined, and no
declaration here applies them to a `WithDim` quantity. No thermodynamic law is proved.

## ii. Key results

- `amountDim_ne_one`, `baseDims_nodup` : amount is not dimensionless, and the amount, length,
  mass, time and temperature dimensions are pairwise distinct.
- `concentrationDim_mul_molarMassDim`, `molarEnergyDim_mul_amount`, `diffusivityDim_mul_time`,
  `stressDim_mul_length_pow_three`, `gasConstantDim_mul_amount_mul_temperature` : the product
  identities.
- `dimScale_round_trip`, `dimScale_ratio`, `dimScale_one_mul` : converting and converting back is
  the identity, ratios are unchanged, and dimensionless coordinates do not rescale.
- `fromISQHom_amountDim`, `fromISQHom_not_injective` : the projection onto `LTMCTDimensionBase`
  forgets amount and has no inverse.
- `amountOfCount_val_mul`, `amountOfCount_nonneg`, `countOfAmount_amountOfCount`,
  `amountOfCount_countOfAmount`, `dimOf_amountOfCount_ne_one`, `gasConstant_pos`,
  `molarEnergy_div`, `molarEnergy_div_molarEnergy` : the constants bridge.
- `celsiusToKelvin_sub_celsiusToKelvin`, `celsiusToKelvin_two_mul_twenty_ne`,
  `celsiusToKelvin_mul_ne` : Celsius readings are affine.
- `logRatio_eq_sub`, `logRatio_self`, `molarEnergyDim_div_gasConstantDim_mul_temperatureDim`,
  `logRatio_dimScale`, `expScaledEnergy_dimScale` : the dimensionless log/exp gate.

## iii. Table of contents

- A. ISQ dimensions of amount-based quantities
- B. Unit conversion and the projection boundary
- C. The constants bridge between counts and amounts
- D. Temperature and the dimensionless log/exp gate

## iv. References

- ISO/IEC 80000-1, *Quantities and units — Part 1: General*: the seven ISQ base quantities.
- IUPAC, *Quantities, Units and Symbols in Physical Chemistry* (the Green Book), abridged 4th
  edition, Royal Society of Chemistry (2023): quantity symbols, molar and molecular quantities,
  temperature and logarithm conventions.
- `Physlib.Units.ISQDimensionBase`, `Physlib.Units.ISQBridge`, `Physlib.Units.ParametricUnits` and
  `Physlib.Units.WithDim.Basic` in https://github.com/leanprover-community/physlib at the root
  package's pin. Physlib's `Constants.kB` fixes the SI value of the Boltzmann constant, so it and
  `Temperature.beta_pos` are cited as analogues but not used.
-/

@[expose] public section

open Dimension

namespace Units.QuantityDimensions

/-! ## A. ISQ dimensions of amount-based quantities -/

/-- The amount-of-substance dimension `N`. -/
def amountDim : Dimension ISQDimensionBase := single .amount

/-- The amount concentration dimension `N L⁻³`. -/
def concentrationDim : Dimension ISQDimensionBase := single .amount / single .length ^ 3

/-- The molar mass dimension `M N⁻¹`. -/
def molarMassDim : Dimension ISQDimensionBase := single .mass / single .amount

/-- The molar energy dimension `M L² T⁻² N⁻¹`, also the dimension of molar chemical potential. -/
def molarEnergyDim : Dimension ISQDimensionBase :=
  (single .mass * single .length ^ 2 / single .time ^ 2) / single .amount

/-- The diffusivity dimension `L² T⁻¹`. -/
def diffusivityDim : Dimension ISQDimensionBase := single .length ^ 2 / single .time

/-- The stress dimension `M L⁻¹ T⁻²`. -/
def stressDim : Dimension ISQDimensionBase := single .mass / (single .length * single .time ^ 2)

/-- The energy dimension `M L² T⁻²`. -/
def energyDim : Dimension ISQDimensionBase := single .mass * single .length ^ 2 / single .time ^ 2

/-- The thermodynamic temperature dimension `Θ`. -/
def temperatureDim : Dimension ISQDimensionBase := single .temperature

/-- The molar gas constant dimension `M L² T⁻² N⁻¹ Θ⁻¹`. -/
def gasConstantDim : Dimension ISQDimensionBase :=
  energyDim / (single .amount * single .temperature)

/-- The exponents of `amountDim` at the seven ISQ base quantities. -/
lemma amountDim_exponent (b : ISQDimensionBase) :
    amountDim.exponent b =
      match b with
      | .length => 0
      | .mass => 0
      | .time => 0
      | .current => 0
      | .temperature => 0
      | .amount => 1
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `concentrationDim` at the seven ISQ base quantities. -/
lemma concentrationDim_exponent (b : ISQDimensionBase) :
    concentrationDim.exponent b =
      match b with
      | .length => -3
      | .mass => 0
      | .time => 0
      | .current => 0
      | .temperature => 0
      | .amount => 1
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `molarMassDim` at the seven ISQ base quantities. -/
lemma molarMassDim_exponent (b : ISQDimensionBase) :
    molarMassDim.exponent b =
      match b with
      | .length => 0
      | .mass => 1
      | .time => 0
      | .current => 0
      | .temperature => 0
      | .amount => -1
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `molarEnergyDim` at the seven ISQ base quantities. -/
lemma molarEnergyDim_exponent (b : ISQDimensionBase) :
    molarEnergyDim.exponent b =
      match b with
      | .length => 2
      | .mass => 1
      | .time => -2
      | .current => 0
      | .temperature => 0
      | .amount => -1
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `diffusivityDim` at the seven ISQ base quantities. -/
lemma diffusivityDim_exponent (b : ISQDimensionBase) :
    diffusivityDim.exponent b =
      match b with
      | .length => 2
      | .mass => 0
      | .time => -1
      | .current => 0
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `stressDim` at the seven ISQ base quantities. -/
lemma stressDim_exponent (b : ISQDimensionBase) :
    stressDim.exponent b =
      match b with
      | .length => -1
      | .mass => 1
      | .time => -2
      | .current => 0
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `energyDim` at the seven ISQ base quantities. -/
lemma energyDim_exponent (b : ISQDimensionBase) :
    energyDim.exponent b =
      match b with
      | .length => 2
      | .mass => 1
      | .time => -2
      | .current => 0
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `temperatureDim` at the seven ISQ base quantities. -/
lemma temperatureDim_exponent (b : ISQDimensionBase) :
    temperatureDim.exponent b =
      match b with
      | .length => 0
      | .mass => 0
      | .time => 0
      | .current => 0
      | .temperature => 1
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `gasConstantDim` at the seven ISQ base quantities. -/
lemma gasConstantDim_exponent (b : ISQDimensionBase) :
    gasConstantDim.exponent b =
      match b with
      | .length => 2
      | .mass => 1
      | .time => -2
      | .current => 0
      | .temperature => -1
      | .amount => -1
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- An amount concentration times a molar mass has the mass density dimension `M L⁻³`. -/
lemma concentrationDim_mul_molarMassDim :
    concentrationDim * molarMassDim = single .mass / single .length ^ 3 := by
  decide

/-- A molar energy times an amount is an energy. -/
lemma molarEnergyDim_mul_amount : molarEnergyDim * single .amount = energyDim := by
  decide

/-- A diffusivity times a time is an area. -/
lemma diffusivityDim_mul_time : diffusivityDim * single .time = single .length ^ 2 := by
  decide

/-- A stress times a volume is an energy. -/
lemma stressDim_mul_length_pow_three : stressDim * single .length ^ 3 = energyDim := by
  decide

/-- The molar gas constant times an amount and a temperature is an energy. -/
lemma gasConstantDim_mul_amount_mul_temperature :
    gasConstantDim * single .amount * single .temperature = energyDim := by
  decide

/-- `Dimension.single` is injective: distinct base quantities have distinct dimensions. -/
lemma single_injective {B : Type} [DimensionBasis B] [DecidableEq B] :
    Function.Injective (single : B → Dimension B) := by
  intro b b' h
  by_contra hne
  have h' := congrArg (fun d => Dimension.exponent d b) h
  simp [single_exponent, hne] at h'

/-- Amount of substance is not dimensionless. -/
lemma amountDim_ne_one : amountDim ≠ 1 := ISQDimensionBase.single_amount_ne_one

/-- The amount, length, mass, time and temperature dimensions are pairwise distinct. -/
lemma baseDims_nodup :
    [amountDim, single .length, single .mass, single .time, temperatureDim].Nodup :=
  (show [ISQDimensionBase.amount, .length, .mass, .time, .temperature].Nodup by decide).map
    single_injective

/-! ## B. Unit conversion and the projection boundary -/

/-- The scaling factor between two unit choices is positive. -/
lemma dimScale_pos {B : Type} [DimensionBasis B] [Fintype B] (u1 u2 : UnitScale B)
    (d : Dimension B) : 0 < u1.dimScale u2 d := by
  simp only [UnitScale.dimScale, MonoidHom.coe_mk, OneHom.coe_mk]
  exact Finset.prod_pos fun b _ => NNReal.rpow_pos (div_pos (u1.scale_pos b) (u2.scale_pos b))

/-- The scaling factor from `u2` back to `u1` is the inverse of the factor from `u1` to `u2`. -/
lemma dimScale_symm {B : Type} [DimensionBasis B] [Fintype B] (u1 u2 : UnitScale B)
    (d : Dimension B) : u2.dimScale u1 d = (u1.dimScale u2 d)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [UnitScale.dimScale_transitive, UnitScale.dimScale_self])

/-- Converting a coordinate from `u1` to `u2` and back returns it. -/
lemma dimScale_round_trip {B : Type} [DimensionBasis B] [Fintype B] (u1 u2 : UnitScale B)
    (d : Dimension B) (x : ℝ) : (u2.dimScale u1 d : ℝ) * ((u1.dimScale u2 d : ℝ) * x) = x := by
  rw [← mul_assoc, ← NNReal.coe_mul, UnitScale.dimScale_transitive, UnitScale.dimScale_self,
    NNReal.coe_one, one_mul]

/-- The ratio of two converted coordinates of one dimension is the ratio of the coordinates. -/
lemma dimScale_ratio {B : Type} [DimensionBasis B] [Fintype B] (u1 u2 : UnitScale B)
    (d : Dimension B) (x y : ℝ) :
    (u1.dimScale u2 d : ℝ) * x / ((u1.dimScale u2 d : ℝ) * y) = x / y :=
  mul_div_mul_left x y (NNReal.coe_pos.mpr (dimScale_pos u1 u2 d)).ne'

/-- A dimensionless coordinate does not rescale. -/
lemma dimScale_one_mul {B : Type} [DimensionBasis B] [Fintype B] (u1 u2 : UnitScale B)
    (x : ℝ) : (u1.dimScale u2 1 : ℝ) * x = x := by
  rw [UnitScale.dimScale_one, NNReal.coe_one, one_mul]

/-- The scaling factor of a base dimension `b` is the ratio of the units chosen at `b`. -/
lemma dimScale_single {B : Type} [DimensionBasis B] [Fintype B] [DecidableEq B]
    (u1 u2 : UnitScale B) (b : B) : u1.dimScale u2 (single b) = u1.scale b / u2.scale b := by
  simp only [UnitScale.dimScale, MonoidHom.coe_mk, OneHom.coe_mk, single_exponent]
  rw [Finset.prod_eq_single b (fun b' _ hb' => by simp [hb']) (by simp)]
  simp

/-- The projection of ISQ dimensions onto `LTMCTDimensionBase` forgets amount of substance. -/
lemma fromISQHom_amountDim : fromISQHom amountDim = 1 := by
  ext b
  cases b <;> simp [amountDim, fromISQHom_apply, fromISQFun, single_exponent]

/-- The projection onto `LTMCTDimensionBase` is not injective, so it has no inverse. -/
lemma fromISQHom_not_injective : ¬ Function.Injective fromISQHom := fun h =>
  amountDim_ne_one (h (fromISQHom_amountDim.trans (map_one fromISQHom).symm))

/-! ## C. The constants bridge between counts and amounts -/

/-- The dimension `d` carried by a quantity `m : WithDim d M`. -/
def dimOf {B : Type} [DimensionBasis B] {d : Dimension B} {M : Type} (_m : WithDim d M) :
    Dimension B := d

/-- The amount of substance `n = N / N_A` of a dimensionless particle count `N`, given the
Avogadro constant `N_A`. -/
noncomputable def amountOfCount (NA N : ℝ) : WithDim amountDim ℝ := ⟨N / NA⟩

/-- The dimensionless particle count `N = n N_A` of an amount of substance `n`. -/
def countOfAmount (NA : ℝ) (n : WithDim amountDim ℝ) : ℝ := n.val * NA

/-- The amount `n = N / N_A` satisfies `n N_A = N`. -/
lemma amountOfCount_val_mul {NA : ℝ} (hNA : 0 < NA) (N : ℝ) :
    (amountOfCount NA N).val * NA = N :=
  div_mul_cancel₀ N hNA.ne'

/-- The amount of a nonnegative particle count is nonnegative. -/
lemma amountOfCount_nonneg {NA N : ℝ} (hNA : 0 < NA) (hN : 0 ≤ N) : 0 ≤ amountOfCount NA N :=
  (WithDim.le_def _ _).mpr (div_nonneg hN hNA.le)

/-- The particle count of the amount of a particle count is that count. -/
lemma countOfAmount_amountOfCount {NA : ℝ} (hNA : 0 < NA) (N : ℝ) :
    countOfAmount NA (amountOfCount NA N) = N :=
  amountOfCount_val_mul hNA N

/-- The amount of the particle count of an amount is that amount. -/
lemma amountOfCount_countOfAmount {NA : ℝ} (hNA : 0 < NA) (n : WithDim amountDim ℝ) :
    amountOfCount NA (countOfAmount NA n) = n :=
  WithDim.ext _ _ (mul_div_cancel_right₀ n.val hNA.ne')

/-- An amount of substance carries the dimension `amountDim`. This holds by construction:
`amountOfCount` takes values in `WithDim amountDim ℝ`. -/
lemma dimOf_amountOfCount (NA N : ℝ) : dimOf (amountOfCount NA N) = amountDim := rfl

/-- Unlike a dimensionless particle count, an amount of substance does not have dimension `1`;
the content is `amountDim_ne_one`. Its coordinate rescales with the amount unit
(`dimScale_single`), while that of a count does not (`dimScale_one_mul`). -/
lemma dimOf_amountOfCount_ne_one (NA N : ℝ) : dimOf (amountOfCount NA N) ≠ 1 :=
  amountDim_ne_one

/-- The molar gas constant `R = N_A k_B`. -/
def gasConstant (NA kB : ℝ) : ℝ := NA * kB

/-- The molar gas constant is positive. -/
lemma gasConstant_pos {NA kB : ℝ} (hNA : 0 < NA) (hkB : 0 < kB) : 0 < gasConstant NA kB :=
  mul_pos hNA hkB

/-- The molar energy `E = N_A e` of a per-particle energy `e`. -/
def molarEnergy (NA e : ℝ) : ℝ := NA * e

/-- The molar energy `E = N_A e` satisfies `E / N_A = e`. -/
lemma molarEnergy_div {NA : ℝ} (hNA : 0 < NA) (e : ℝ) : molarEnergy NA e / NA = e :=
  mul_div_cancel_left₀ e hNA.ne'

/-- The per-particle energy `e = E / N_A` of a molar energy `E` satisfies `N_A e = E`. -/
lemma molarEnergy_div_molarEnergy {NA : ℝ} (hNA : 0 < NA) (E : ℝ) : molarEnergy NA (E / NA) = E :=
  mul_div_cancel₀ E hNA.ne'

/-- The dimension `N⁻¹` of `N_A` times an energy dimension is the dimension of `E = N_A e`. -/
lemma inv_amountDim_mul_energyDim : amountDim⁻¹ * energyDim = molarEnergyDim := by
  decide

/-- The dimension `N⁻¹` of `N_A` times the dimension of `k_B` is the dimension of
`R = N_A k_B`. -/
lemma inv_amountDim_mul_energyDim_div_temperatureDim :
    amountDim⁻¹ * (energyDim / temperatureDim) = gasConstantDim := by
  decide

/-! ## D. Temperature and the dimensionless log/exp gate -/

/-- The Kelvin value `tC + 273.15` of a Celsius reading `tC`. -/
def celsiusToKelvin (tC : ℝ) : ℝ := tC + 273.15

/-- Kelvin differences equal Celsius differences. -/
lemma celsiusToKelvin_sub_celsiusToKelvin (t1 t2 : ℝ) :
    celsiusToKelvin t2 - celsiusToKelvin t1 = t2 - t1 := by
  simp only [celsiusToKelvin]
  ring

/-- Scaling a Celsius reading by `c ≠ 1` does not scale its Kelvin value by `c`. -/
lemma celsiusToKelvin_mul_ne (t : ℝ) {c : ℝ} (hc : c ≠ 1) :
    celsiusToKelvin (c * t) ≠ c * celsiusToKelvin t := by
  intro h
  apply hc
  simp only [celsiusToKelvin] at h
  linear_combination (-1 / 273.15 : ℝ) * h

/-- Doubling the Celsius reading `20` does not double its Kelvin value. -/
lemma celsiusToKelvin_two_mul_twenty_ne :
    celsiusToKelvin (2 * 20) ≠ 2 * celsiusToKelvin 20 := by
  norm_num [celsiusToKelvin]

/-- The inverse temperature `1 / (k_B T)` is positive when `k_B > 0` and `T > 0`. Physlib's
`Temperature.beta_pos` is the analogue for its fixed constant `Constants.kB`. -/
lemma inverseTemperature_pos {kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) : 0 < 1 / (kB * T) :=
  one_div_pos.mpr (mul_pos hkB hT)

/-- The logarithm `log (x / x0)` of the ratio of two positive reals. The arguments are bare
reals: the intended use is two coordinates of one dimension in one unit choice, whose ratio is
dimensionless, so that `logRatio` is unchanged by a change of units (`logRatio_dimScale`). -/
noncomputable def logRatio (x x0 : ℝ) (_hx : 0 < x) (_hx0 : 0 < x0) : ℝ := Real.log (x / x0)

/-- `logRatio x x0` is `log x - log x0`. -/
lemma logRatio_eq_sub {x x0 : ℝ} (hx : 0 < x) (hx0 : 0 < x0) :
    logRatio x x0 hx hx0 = Real.log x - Real.log x0 :=
  Real.log_div hx.ne' hx0.ne'

/-- The `logRatio` of a coordinate to itself is `0`. -/
lemma logRatio_self {x : ℝ} (hx : 0 < x) : logRatio x x hx hx = 0 := by
  rw [logRatio, div_self hx.ne', Real.log_one]

/-- The `logRatio` of coordinates with ratio `1` is `0`. -/
lemma logRatio_eq_zero_of_div_eq_one {x x0 : ℝ} (hx : 0 < x) (hx0 : 0 < x0) (h : x / x0 = 1) :
    logRatio x x0 hx hx0 = 0 := by
  rw [logRatio, h, Real.log_one]

/-- `logRatio` is unchanged by a change of units. -/
lemma logRatio_dimScale {B : Type} [DimensionBasis B] [Fintype B] (u1 u2 : UnitScale B)
    (d : Dimension B) {x x0 : ℝ} (hx : 0 < x) (hx0 : 0 < x0) :
    logRatio ((u1.dimScale u2 d : ℝ) * x) ((u1.dimScale u2 d : ℝ) * x0)
        (mul_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 d)) hx)
        (mul_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 d)) hx0) =
      logRatio x x0 hx hx0 := by
  simp only [logRatio, dimScale_ratio]

/-- The exponent `E / (R T)` of a molar energy over a gas constant and a temperature is
dimensionless. -/
lemma molarEnergyDim_div_gasConstantDim_mul_temperatureDim :
    molarEnergyDim / (gasConstantDim * temperatureDim) = 1 := by
  decide

/-- The Boltzmann/Arrhenius-style factor `exp (-(E / (R T)))` for real coordinates of a molar
energy `E`, a gas constant `R > 0` and an absolute temperature `T > 0`. The exponent is
dimensionless by `molarEnergyDim_div_gasConstantDim_mul_temperatureDim`, so the factor is
unchanged by a change of units (`expScaledEnergy_dimScale`). -/
noncomputable def expScaledEnergy (E R T : ℝ) (_hR : 0 < R) (_hT : 0 < T) : ℝ :=
  Real.exp (-(E / (R * T)))

/-- `expScaledEnergy` is unchanged by a change of units. -/
lemma expScaledEnergy_dimScale (u1 u2 : UnitScale ISQDimensionBase) (E : ℝ) {R T : ℝ}
    (hR : 0 < R) (hT : 0 < T) :
    expScaledEnergy ((u1.dimScale u2 molarEnergyDim : ℝ) * E)
        ((u1.dimScale u2 gasConstantDim : ℝ) * R) ((u1.dimScale u2 temperatureDim : ℝ) * T)
        (mul_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 gasConstantDim)) hR)
        (mul_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 temperatureDim)) hT) =
      expScaledEnergy E R T hR hT := by
  have hE : (u1.dimScale u2 molarEnergyDim : ℝ) =
      (u1.dimScale u2 gasConstantDim : ℝ) * (u1.dimScale u2 temperatureDim : ℝ) := by
    rw [← NNReal.coe_mul, ← map_mul,
      div_eq_one.mp molarEnergyDim_div_gasConstantDim_mul_temperatureDim]
  have hne : (u1.dimScale u2 gasConstantDim : ℝ) * (u1.dimScale u2 temperatureDim : ℝ) ≠ 0 :=
    (mul_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 gasConstantDim))
      (NNReal.coe_pos.mpr (dimScale_pos u1 u2 temperatureDim))).ne'
  simp only [expScaledEnergy]
  rw [hE, mul_mul_mul_comm, mul_div_mul_left _ _ hne]

/-- For `E = N_A e` and `R = N_A k_B`, `expScaledEnergy E R T` is `exp (-(e / (k_B T)))`. -/
lemma expScaledEnergy_molarEnergy_gasConstant {NA kB : ℝ} (hNA : 0 < NA) (hkB : 0 < kB)
    (e : ℝ) {T : ℝ} (hT : 0 < T) :
    expScaledEnergy (molarEnergy NA e) (gasConstant NA kB) T (gasConstant_pos hNA hkB) hT =
      Real.exp (-(e / (kB * T))) := by
  rw [expScaledEnergy, molarEnergy, gasConstant, mul_assoc, mul_div_mul_left _ _ hNA.ne']

end Units.QuantityDimensions
