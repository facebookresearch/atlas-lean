/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Units.QuantityDimensions

/-!
# Tests for `PhyslibExt.Units.QuantityDimensions`

* the exponents of every amount-based dimension at all seven ISQ base quantities, and the product
  identities;
* the rescaling of a concentration coordinate by `1000⁻³` between unit scales differing by a
  factor `1000` on length only, and of an amount coordinate by `1000` from moles to millimoles,
  while a dimensionless count does not rescale;
* the projection boundary `fromISQHom (single .amount) = 1`;
* the count–amount round trips, with the arithmetic probe `N_A = 2`, which is not the SI value;
* the Celsius difference identity and doubling counterexample, and the `T = 0` boundary;
* the dimensionless log/exp gate.
-/

@[expose] public section

namespace PhyslibExtTest.Units.QuantityDimensions

open Dimension _root_.Units.QuantityDimensions

/-! ## A. Exponents and products -/

-- `amountDim = N`.
example :
    amountDim.exponent .length = 0 ∧ amountDim.exponent .mass = 0 ∧
      amountDim.exponent .time = 0 ∧ amountDim.exponent .current = 0 ∧
      amountDim.exponent .temperature = 0 ∧ amountDim.exponent .amount = 1 ∧
      amountDim.exponent .luminousIntensity = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact amountDim_exponent _

-- `concentrationDim = N L⁻³`.
example :
    concentrationDim.exponent .length = -3 ∧ concentrationDim.exponent .mass = 0 ∧
      concentrationDim.exponent .time = 0 ∧ concentrationDim.exponent .current = 0 ∧
      concentrationDim.exponent .temperature = 0 ∧ concentrationDim.exponent .amount = 1 ∧
      concentrationDim.exponent .luminousIntensity = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact concentrationDim_exponent _

-- `molarMassDim = M N⁻¹`.
example :
    molarMassDim.exponent .length = 0 ∧ molarMassDim.exponent .mass = 1 ∧
      molarMassDim.exponent .time = 0 ∧ molarMassDim.exponent .current = 0 ∧
      molarMassDim.exponent .temperature = 0 ∧ molarMassDim.exponent .amount = -1 ∧
      molarMassDim.exponent .luminousIntensity = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact molarMassDim_exponent _

-- `molarEnergyDim = M L² T⁻² N⁻¹`.
example :
    molarEnergyDim.exponent .length = 2 ∧ molarEnergyDim.exponent .mass = 1 ∧
      molarEnergyDim.exponent .time = -2 ∧ molarEnergyDim.exponent .current = 0 ∧
      molarEnergyDim.exponent .temperature = 0 ∧ molarEnergyDim.exponent .amount = -1 ∧
      molarEnergyDim.exponent .luminousIntensity = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact molarEnergyDim_exponent _

-- `diffusivityDim = L² T⁻¹`.
example :
    diffusivityDim.exponent .length = 2 ∧ diffusivityDim.exponent .mass = 0 ∧
      diffusivityDim.exponent .time = -1 ∧ diffusivityDim.exponent .current = 0 ∧
      diffusivityDim.exponent .temperature = 0 ∧ diffusivityDim.exponent .amount = 0 ∧
      diffusivityDim.exponent .luminousIntensity = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact diffusivityDim_exponent _

-- `stressDim = M L⁻¹ T⁻²`.
example :
    stressDim.exponent .length = -1 ∧ stressDim.exponent .mass = 1 ∧
      stressDim.exponent .time = -2 ∧ stressDim.exponent .current = 0 ∧
      stressDim.exponent .temperature = 0 ∧ stressDim.exponent .amount = 0 ∧
      stressDim.exponent .luminousIntensity = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact stressDim_exponent _

-- `energyDim = M L² T⁻²`.
example :
    energyDim.exponent .length = 2 ∧ energyDim.exponent .mass = 1 ∧
      energyDim.exponent .time = -2 ∧ energyDim.exponent .current = 0 ∧
      energyDim.exponent .temperature = 0 ∧ energyDim.exponent .amount = 0 ∧
      energyDim.exponent .luminousIntensity = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact energyDim_exponent _

-- `temperatureDim = Θ`.
example :
    temperatureDim.exponent .length = 0 ∧ temperatureDim.exponent .mass = 0 ∧
      temperatureDim.exponent .time = 0 ∧ temperatureDim.exponent .current = 0 ∧
      temperatureDim.exponent .temperature = 1 ∧ temperatureDim.exponent .amount = 0 ∧
      temperatureDim.exponent .luminousIntensity = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact temperatureDim_exponent _

-- `gasConstantDim = M L² T⁻² N⁻¹ Θ⁻¹`.
example :
    gasConstantDim.exponent .length = 2 ∧ gasConstantDim.exponent .mass = 1 ∧
      gasConstantDim.exponent .time = -2 ∧ gasConstantDim.exponent .current = 0 ∧
      gasConstantDim.exponent .temperature = -1 ∧ gasConstantDim.exponent .amount = -1 ∧
      gasConstantDim.exponent .luminousIntensity = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact gasConstantDim_exponent _

example : concentrationDim * molarMassDim = single .mass / single .length ^ 3 :=
  concentrationDim_mul_molarMassDim

example : molarEnergyDim * single .amount = energyDim := molarEnergyDim_mul_amount

example : diffusivityDim * single .time = single .length ^ 2 := diffusivityDim_mul_time

example : stressDim * single .length ^ 3 = energyDim := stressDim_mul_length_pow_three

example : gasConstantDim * single .amount * single .temperature = energyDim :=
  gasConstantDim_mul_amount_mul_temperature

-- The definitions are exposed: identities also evaluate by `decide` downstream.
example : concentrationDim * molarMassDim = single .mass / single .length ^ 3 := by decide

-- Amount is not dimensionless, and is distinct from the other base dimensions.
example : single (.amount : ISQDimensionBase) ≠ 1 := amountDim_ne_one

example : [amountDim, single .length, single .mass, single .time, temperatureDim].Nodup :=
  baseDims_nodup

example : amountDim ≠ single .length := fun h => absurd (single_injective h) (by decide)

example : amountDim ≠ temperatureDim := fun h => absurd (single_injective h) (by decide)

/-! ## B. Unit conversion -/

/-- Unit scales whose length unit is `1000` times larger, as for kilometres against metres. -/
def kiloLengthScale : UnitScale ISQDimensionBase :=
  ⟨fun b => if b = .length then 1000 else 1, fun b => by split_ifs <;> norm_num⟩

/-- Unit scales whose amount unit is `1000` times smaller, as for millimoles against moles. -/
noncomputable def milliAmountScale : UnitScale ISQDimensionBase :=
  ⟨fun b => if b = .amount then 1 / 1000 else 1, fun b => by split_ifs <;> norm_num⟩

/-- The unit scales with every unit of magnitude `1`. -/
def oneScale : UnitScale ISQDimensionBase := ⟨fun _ => 1, fun _ => one_pos⟩

/-- Changing from `kiloLengthScale` to `oneScale` rescales a concentration by `1000⁻³`. -/
lemma dimScale_kiloLengthScale_concentrationDim :
    (kiloLengthScale.dimScale oneScale concentrationDim : ℝ) = (1000 : ℝ) ^ (-3 : ℤ) := by
  simp only [UnitScale.dimScale, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Finset.prod_eq_single ISQDimensionBase.length
    (fun b _ hb => by simp [kiloLengthScale, oneScale, hb]) (by simp)]
  have h : ((concentrationDim.exponent .length : ℚ) : ℝ) = -3 := by
    rw [concentrationDim_exponent]
    norm_num
  simp only [kiloLengthScale, oneScale, ↓reduceIte, div_one, NNReal.coe_rpow, NNReal.coe_ofNat, h]
  norm_num [Real.rpow_neg, Real.rpow_natCast]

-- A concentration coordinate `x` in `N (1000 L)⁻³` is `1000⁻³ x` in `N L⁻³`.
example (x : ℝ) :
    (kiloLengthScale.dimScale oneScale concentrationDim : ℝ) * x = (1000 : ℝ) ^ (-3 : ℤ) * x := by
  rw [dimScale_kiloLengthScale_concentrationDim]

example : (1000 : ℝ) ^ (-3 : ℤ) = 1 / 1000000000 := by norm_num

-- Converting the concentration coordinate there and back returns it.
example (x : ℝ) :
    (oneScale.dimScale kiloLengthScale concentrationDim : ℝ) *
      ((kiloLengthScale.dimScale oneScale concentrationDim : ℝ) * x) = x :=
  dimScale_round_trip _ _ _ x

example : oneScale.dimScale kiloLengthScale concentrationDim =
    (kiloLengthScale.dimScale oneScale concentrationDim)⁻¹ :=
  dimScale_symm _ _ _

-- Physlib's transitivity and self laws elaborate over the ISQ basis.
example (d : Dimension ISQDimensionBase) :
    kiloLengthScale.dimScale oneScale d * oneScale.dimScale milliAmountScale d =
      kiloLengthScale.dimScale milliAmountScale d :=
  UnitScale.dimScale_transitive _ _ _ d

example (d : Dimension ISQDimensionBase) : kiloLengthScale.dimScale kiloLengthScale d = 1 :=
  UnitScale.dimScale_self _ d

-- Ratios of coordinates of one dimension are unchanged, and dimensionless coordinates do not
-- rescale.
example (x y : ℝ) :
    (kiloLengthScale.dimScale oneScale concentrationDim : ℝ) * x /
      ((kiloLengthScale.dimScale oneScale concentrationDim : ℝ) * y) = x / y :=
  dimScale_ratio _ _ _ x y

example (x : ℝ) : (kiloLengthScale.dimScale oneScale 1 : ℝ) * x = x := dimScale_one_mul _ _ x

-- From moles to millimoles an amount coordinate rescales by `1000`, while a dimensionless count
-- does not rescale.
example : (oneScale.dimScale milliAmountScale amountDim : ℝ) = 1000 := by
  rw [amountDim, dimScale_single]
  norm_num [oneScale, milliAmountScale]

example (N : ℝ) : (oneScale.dimScale milliAmountScale 1 : ℝ) * N = N := dimScale_one_mul _ _ N

-- The projection onto `LTMCTDimensionBase` forgets amount, so it is not injective.
example : fromISQHom (single .amount) = 1 := fromISQHom_amountDim

example : ¬ Function.Injective fromISQHom := fromISQHom_not_injective

/-! ## C. The constants bridge -/

-- With `N = N_A` the amount is `n = 1`, and counting its particles returns `N_A`.
example {NA : ℝ} (hNA : 0 < NA) : (amountOfCount NA NA).val = 1 := div_self hNA.ne'

example {NA : ℝ} (hNA : 0 < NA) : countOfAmount NA (amountOfCount NA NA) = NA :=
  countOfAmount_amountOfCount hNA NA

example {NA : ℝ} (hNA : 0 < NA) (N : ℝ) : (amountOfCount NA N).val * NA = N :=
  amountOfCount_val_mul hNA N

example {NA N : ℝ} (hNA : 0 < NA) (hN : 0 ≤ N) : 0 ≤ (amountOfCount NA N).val :=
  amountOfCount_nonneg hNA hN

example {NA : ℝ} (hNA : 0 < NA) (n : WithDim amountDim ℝ) :
    amountOfCount NA (countOfAmount NA n) = n :=
  amountOfCount_countOfAmount hNA n

-- An amount carries the amount dimension; a count carries none.
example (NA N : ℝ) : dimOf (amountOfCount NA N) = amountDim := dimOf_amountOfCount NA N

example (NA N : ℝ) : dimOf (amountOfCount NA N) ≠ 1 := dimOf_amountOfCount_ne_one NA N

-- Arithmetic probe `N_A = 2`, not the SI value: `6` particles are the amount `3`.
example : (amountOfCount 2 6).val = 3 := by norm_num [amountOfCount]

example : countOfAmount 2 (amountOfCount 2 6) = 6 := countOfAmount_amountOfCount two_pos 6

example {NA kB : ℝ} (hNA : 0 < NA) (hkB : 0 < kB) : 0 < gasConstant NA kB :=
  gasConstant_pos hNA hkB

-- `E / N_A = e` for a symbolic positive `N_A`, and for the probe `N_A = 2`.
example {NA : ℝ} (hNA : 0 < NA) (e : ℝ) : molarEnergy NA e / NA = e := molarEnergy_div hNA e

example : molarEnergy 2 5 = 10 := by norm_num [molarEnergy]

example : molarEnergy 2 5 / 2 = 5 := molarEnergy_div two_pos 5

-- `N_A (E / N_A) = E` for a symbolic positive `N_A`, and for the arithmetic probe `N_A = 2`
-- (not the SI value): the molar energy of `7 / 2` is `7`.
example {NA : ℝ} (hNA : 0 < NA) (E : ℝ) :
    molarEnergy NA (E / NA) = E ∧ molarEnergy 2 (7 / 2) = 7 :=
  ⟨molarEnergy_div_molarEnergy hNA E, molarEnergy_div_molarEnergy two_pos 7⟩

example : amountDim⁻¹ * energyDim = molarEnergyDim := inv_amountDim_mul_energyDim

example : amountDim⁻¹ * (energyDim / temperatureDim) = gasConstantDim :=
  inv_amountDim_mul_energyDim_div_temperatureDim

/-! ## D. Temperature and the log/exp gate -/

example (t1 t2 : ℝ) : celsiusToKelvin t2 - celsiusToKelvin t1 = t2 - t1 :=
  celsiusToKelvin_sub_celsiusToKelvin t1 t2

example : celsiusToKelvin 20 = 293.15 := by norm_num [celsiusToKelvin]

example : celsiusToKelvin (2 * 20) ≠ 2 * celsiusToKelvin 20 := by norm_num [celsiusToKelvin]

example : celsiusToKelvin (2 * 20) ≠ 2 * celsiusToKelvin 20 := celsiusToKelvin_two_mul_twenty_ne

example : celsiusToKelvin (2 * 20) ≠ 2 * celsiusToKelvin 20 :=
  celsiusToKelvin_mul_ne 20 (by norm_num)

example {kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) : 0 < 1 / (kB * T) :=
  inverseTemperature_pos hkB hT

-- At `T = 0` the expression `1 / (k_B T)` is `0` in Lean, so the hypothesis `T > 0` is needed.
example (kB : ℝ) : ¬ 0 < 1 / (kB * 0) := by simp

example {x : ℝ} (hx : 0 < x) : logRatio x x hx hx = 0 := logRatio_self hx

example {x x0 : ℝ} (hx : 0 < x) (hx0 : 0 < x0) :
    logRatio x x0 hx hx0 = Real.log x - Real.log x0 :=
  logRatio_eq_sub hx hx0

example : logRatio 3 3 (by norm_num) (by norm_num) = 0 :=
  logRatio_eq_zero_of_div_eq_one _ _ (by norm_num)

example {x x0 : ℝ} (hx : 0 < x) (hx0 : 0 < x0) :
    logRatio ((kiloLengthScale.dimScale oneScale concentrationDim : ℝ) * x)
        ((kiloLengthScale.dimScale oneScale concentrationDim : ℝ) * x0)
        (mul_pos (NNReal.coe_pos.mpr (dimScale_pos _ _ _)) hx)
        (mul_pos (NNReal.coe_pos.mpr (dimScale_pos _ _ _)) hx0) =
      logRatio x x0 hx hx0 :=
  logRatio_dimScale _ _ _ hx hx0

example : molarEnergyDim / (gasConstantDim * temperatureDim) = 1 :=
  molarEnergyDim_div_gasConstantDim_mul_temperatureDim

example {R T : ℝ} (hR : 0 < R) (hT : 0 < T) : expScaledEnergy 0 R T hR hT = 1 := by
  simp [expScaledEnergy]

example (E : ℝ) {R T : ℝ} (hR : 0 < R) (hT : 0 < T) :
    expScaledEnergy ((kiloLengthScale.dimScale oneScale molarEnergyDim : ℝ) * E)
        ((kiloLengthScale.dimScale oneScale gasConstantDim : ℝ) * R)
        ((kiloLengthScale.dimScale oneScale temperatureDim : ℝ) * T)
        (mul_pos (NNReal.coe_pos.mpr (dimScale_pos _ _ _)) hR)
        (mul_pos (NNReal.coe_pos.mpr (dimScale_pos _ _ _)) hT) =
      expScaledEnergy E R T hR hT :=
  expScaledEnergy_dimScale _ _ E hR hT

example {NA kB : ℝ} (hNA : 0 < NA) (hkB : 0 < kB) (e : ℝ) {T : ℝ} (hT : 0 < T) :
    expScaledEnergy (molarEnergy NA e) (gasConstant NA kB) T (gasConstant_pos hNA hkB) hT =
      Real.exp (-(e / (kB * T))) :=
  expScaledEnergy_molarEnergy_gasConstant hNA hkB e hT

end PhyslibExtTest.Units.QuantityDimensions
