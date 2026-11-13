/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Chemistry.QuantityCalculus
public import Physlib.Units.SIUnitChoices

/-!
# Tests for `PhyslibExt.Chemistry.QuantityCalculus`

* Quantity kinds: the exponents of concentration and molar mass; concentration is not
  dimensionless; a concentration of `0.01 mol/L` is `10 mol/m³`, and its raw logarithm changes
  with the unit while `logRatio` does not.
* The exponent-vector bridge: `dimensionOfVector` and `exponentVector` are inverse.
* `logRatio`: with `c = 0.01` and `c° = 1`, `logRatio c c°` is `Real.log 0.01`; the logarithm of
  the ratio of equal values is `0`; the ratio `c / c°` of two concentrations is dimensionless,
  and the ratio of a concentration to a molar mass is not.
* Dimensionless groups: the exponent matrix of diffusivity, length and time over the rows length
  and time has rank `2` and a one-dimensional kernel containing the exponents `(1, -2, 1)` of the
  Fourier number `D t / L²`, which is dimensionless over the seven ISQ base quantities.
* Celsius: `25 °C` converts to the absolute temperature `298.15 K`; the
  Boltzmann factor for `E / kB = 1000 K` is `exp (-1000 / 298.15)`.
  Raw Celsius numbers and wrong dimensions are rejected. Absolute zero can
  be converted but is excluded from the factor; negative Celsius readings
  above absolute zero remain valid.
-/

@[expose] public section

namespace PhyslibExtTest.Chemistry.QuantityCalculus

open Matrix _root_.Chemistry.QuantityCalculus
open scoped NNReal

/-! ## A. Quantity kinds and changes of units -/

-- Concentration has exponent `1` at amount of substance and `-3` at length.
example : exponentVector concentration 5 = 1 ∧ exponentVector concentration 0 = -3 := by
  simp [concentration_eq]

-- Molar mass has exponent `1` at mass and `-1` at amount of substance.
example : exponentVector molarMass 1 = 1 ∧ exponentVector molarMass 5 = -1 := by
  simp [molarMass_eq]

-- Concentration is not dimensionless.
example : ¬ IsDimensionless concentration := by
  intro h
  have h5 := congrFun (congrArg exponentVector (isDimensionless_iff.mp h)) 5
  simp [concentration_eq, exponentVector_one] at h5

-- The exponent-vector bridge is an equivalence, on a sample vector and on a kind.
example (v : Fin 7 → ℚ) : exponentVector (dimensionOfVector v) = v :=
  exponentVector_dimensionOfVector v

example : dimensionOfVector (exponentVector concentration) = concentration :=
  dimensionOfVector_exponentVector concentration

/-- The magnitudes of the decimetre unit choice: `1 / 10` at length, `1` elsewhere. -/
noncomputable def decimetreScaleScale : ISQDimensionBase → ℝ≥0
  | .length => 1 / 10
  | .mass => 1
  | .time => 1
  | .current => 1
  | .temperature => 1
  | .amount => 1
  | .luminousIntensity => 1

/-- Every decimetre-scale magnitude is positive. -/
lemma decimetreScaleScale_pos (b : ISQDimensionBase) : 0 < decimetreScaleScale b := by
  cases b <;> norm_num [decimetreScaleScale]

/-- The unit choice with the decimetre as the unit of length and the coherent SI units
elsewhere: one decimetre is `1 / 10` metre. -/
noncomputable def decimetreScale : UnitScale ISQDimensionBase where
  scale := decimetreScaleScale
  scale_pos := decimetreScaleScale_pos

@[simp] lemma decimetreScale_scale_apply (b : ISQDimensionBase) :
    decimetreScale.scale b = decimetreScaleScale b :=
  rfl

/-- The coherent SI unit choice: metre, kilogram, second, ampere, kelvin, mole, candela,
all of magnitude `1`. -/
def metreScale : UnitScale ISQDimensionBase where
  scale := fun _ => 1
  scale_pos := fun _ => one_pos

@[simp] lemma metreScale_scale_apply (b : ISQDimensionBase) : metreScale.scale b = 1 := rfl

/-- The decimetre unit choice rescales a length by `1 / 10`. -/
lemma unitFactor_decimetreScale_length :
    unitFactor decimetreScale metreScale length = 1 / 10 := by
  rw [unitFactor_eq_prod, prod_univ_ISQDimensionBase]
  have hl : ∀ b : ISQDimensionBase, ((length.exponent b : ℚ) : ℝ) =
      if b = .length then 1 else 0 := by
    intro b
    cases b <;> simp [length, Dimension.single_exponent]
  simp [hl, decimetreScaleScale]

/-- The decimetre unit choice does not rescale an amount of substance. -/
lemma unitFactor_decimetreScale_amount :
    unitFactor decimetreScale metreScale amount = 1 := by
  rw [unitFactor_eq_prod, prod_univ_ISQDimensionBase]
  have ha : ∀ b : ISQDimensionBase, ((amount.exponent b : ℚ) : ℝ) =
      if b = .amount then 1 else 0 := by
    intro b
    cases b <;> simp [amount, Dimension.single_exponent]
  simp [ha, decimetreScaleScale]

/-- A concentration of `0.01 mol/L = 0.01 mol/dm³` is `10 mol/m³`. -/
lemma rescale_decimetreToMetre_concentration :
    rescale decimetreScale metreScale concentration 0.01 = 10 := by
  have hconc : unitFactor decimetreScale metreScale concentration = 1000 := by
    rw [concentration, unitFactor_div, unitFactor_pow, unitFactor_decimetreScale_amount,
      unitFactor_decimetreScale_length]
    norm_num
  rw [rescale, hconc]
  norm_num

-- The raw logarithm of the numerical value of a concentration depends on the unit.
example : Real.log (rescale decimetreScale metreScale concentration 0.01) ≠ Real.log 0.01 := by
  rw [rescale_decimetreToMetre_concentration]
  exact (Real.log_lt_log (by norm_num) (by norm_num)).ne'

-- The logarithm of the ratio of two concentrations does not.
example : logRatio
    ((unitFactor decimetreScale metreScale concentration) •
      (⟨0.01⟩ : WithDim concentration ℝ))
    ((unitFactor decimetreScale metreScale concentration) •
      (⟨1⟩ : WithDim concentration ℝ))
    (by rw [WithDim.real_smul_val, smul_eq_mul]
        exact mul_pos (unitFactor_pos decimetreScale metreScale concentration)
          (by norm_num))
    (by rw [WithDim.real_smul_val, smul_eq_mul]
        exact mul_pos (unitFactor_pos decimetreScale metreScale concentration) one_pos) =
    logRatio (⟨0.01⟩ : WithDim concentration ℝ) (⟨1⟩ : WithDim concentration ℝ)
      (by norm_num) one_pos :=
  logRatio_rescale decimetreScale metreScale (by norm_num) one_pos

-- A ratio of two values of the same kind is unchanged by the change of units.
example : rescale decimetreScale metreScale pressure 3 /
    rescale decimetreScale metreScale pressure 2 = 3 / 2 :=
  rescale_div_rescale_same decimetreScale metreScale pressure 3 2

-- Converting to the new units and back recovers the value.
example : rescale metreScale decimetreScale concentration
    (rescale decimetreScale metreScale concentration 0.01) = 0.01 := by
  rw [rescale_transitive, rescale_self]

/-! ## B. Logarithms of ratios -/

-- `ln (c / c°)` with `c = 0.01` and `c° = 1`.
example : logRatio (⟨0.01⟩ : WithDim concentration ℝ) (⟨1⟩ : WithDim concentration ℝ)
    (by norm_num) one_pos = Real.log 0.01 := by
  simp [logRatio]

-- The logarithm of the ratio of equal values is `0`.
example : logRatio (⟨0.01⟩ : WithDim concentration ℝ)
    (⟨0.01⟩ : WithDim concentration ℝ) (by norm_num) (by norm_num) = 0 :=
  logRatio_self _

example (x : WithDim concentration ℝ) (hx : 0 < x.val) : logRatio x x hx hx = 0 :=
  logRatio_self hx

-- `ln (c / c°) = ln c - ln c°`.
example : logRatio (⟨0.01⟩ : WithDim concentration ℝ) (⟨1⟩ : WithDim concentration ℝ)
    (by norm_num) one_pos = Real.log 0.01 - Real.log 1 :=
  logRatio_eq_log_sub_log _ _

-- The ratio `c / c°` of two concentrations is dimensionless.
example : IsDimensionless (concentration / concentration) :=
  isDimensionless_div_iff.mpr rfl

-- So is the ratio of `p / c` to a chemical potential.
example : IsDimensionless (pressure / concentration / chemicalPotential) :=
  isDimensionless_div_iff.mpr pressure_div_concentration

-- The ratio of a concentration to a molar mass is not.
example : ¬ IsDimensionless (concentration / molarMass) := by
  intro h
  have h2 : exponentVector (concentration / molarMass) = 0 := by
    rw [isDimensionless_iff.mp h, exponentVector_one]
  have h1 := congrFun h2 1
  rw [exponentVector_div, concentration_eq, molarMass_eq] at h1
  simp at h1

/-! ## C. Dimensionless groups -/

/-- The exponent matrix of diffusivity, length and time (columns) over the base quantities
length and time (rows). -/
def fourierMatrix : Matrix (Fin 2) (Fin 3) ℚ := !![2, 1, 0; -1, 0, 1]

/-- The exponents `(1, -2, 1)` of the Fourier number `D t / L²` in diffusivity `D`, length `L`
and time `t`. -/
def fourierExponents : Fin 3 → ℚ := ![1, -2, 1]

example : fourierMatrix *ᵥ fourierExponents = 0 := by
  ext i
  fin_cases i <;> norm_num [fourierMatrix, fourierExponents, mulVec, dotProduct,
    Fin.sum_univ_succ]

example : fourierExponents ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [fourierExponents] at h0

example : fourierExponents ∈ LinearMap.ker fourierMatrix.mulVecLin := by
  rw [mem_ker_mulVecLin_iff]
  ext i
  fin_cases i <;> norm_num [fourierMatrix, fourierExponents, mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- Every pair of length and time exponents is reached: `![0, w 0, w 1]` maps to `w`. -/
lemma fourierMatrix_mulVecLin_surjective : Function.Surjective fourierMatrix.mulVecLin := by
  intro w
  refine ⟨![0, w 0, w 1], ?_⟩
  ext i
  fin_cases i <;> simp [fourierMatrix, mulVec, dotProduct, Fin.sum_univ_succ]

/-- The exponent matrix of diffusivity, length and time has rank `2`. -/
lemma fourierMatrix_rank : fourierMatrix.rank = 2 := by
  rw [Matrix.rank, LinearMap.range_eq_top.mpr fourierMatrix_mulVecLin_surjective, finrank_top,
    Module.finrank_fin_fun]

/-- Its kernel, the space of exponents of dimensionless groups, has dimension `3 - 2 = 1`. -/
lemma finrank_ker_fourierMatrix :
    Module.finrank ℚ (LinearMap.ker fourierMatrix.mulVecLin) = 1 := by
  rw [finrank_ker_mulVecLin, fourierMatrix_rank]

example : Module.finrank ℚ (LinearMap.ker fourierMatrix.mulVecLin) +
    Module.finrank ℚ (LinearMap.range fourierMatrix.mulVecLin) = 3 :=
  finrank_ker_add_finrank_range fourierMatrix

/-- The exponent matrix whose columns are `diffusivity`, `length` and `time`, over the seven ISQ
base quantities. -/
def fourierISQMatrix : Matrix (Fin 7) (Fin 3) ℚ :=
  Matrix.of fun i j => (exponentVector (![diffusivity, length, time] j)) i

/-- The Fourier exponents lie in the kernel of the ISQ exponent matrix. -/
lemma fourierExponents_mem_ker_fourierISQMatrix :
    fourierExponents ∈ LinearMap.ker fourierISQMatrix.mulVecLin := by
  rw [mem_ker_mulVecLin_iff]
  ext i
  fin_cases i <;> simp [fourierISQMatrix, fourierExponents, diffusivity_eq, length_eq,
    time_eq, mulVec, dotProduct, Fin.sum_univ_succ]

example : IsDimensionless (dimensionOfVector (fourierISQMatrix *ᵥ fourierExponents)) := by
  rw [isDimensionless_mulVec_iff]
  exact fourierExponents_mem_ker_fourierISQMatrix

-- The same through the monomial convention: `D` times `L⁻²` times `t` has dimension `1`.
example : diffusivity * (length ^ (2 : ℕ))⁻¹ * time = 1 := by
  apply Dimension.ext
  intro b
  cases b <;>
    simp [diffusivity, length, time, Dimension.mul_exponent, Dimension.div_exponent,
      Dimension.inv_exponent, Dimension.npow_exponent, Dimension.single_exponent]

/-! ## D. Celsius temperature -/

example : (celsiusToKelvin 25 (by norm_num)).toReal = 298.15 := by
  change (25 : ℝ) + 273.15 = 298.15
  norm_num

example : (celsiusToKelvin 25 (by norm_num)).toReal ≠ 25 :=
  celsiusToKelvin_ne_self 25 (by norm_num)

example : kelvinToCelsius (Temperature.ofRealNonneg 298.15 (by norm_num)) = 25 := by
  change (298.15 : ℝ) - 273.15 = 25
  norm_num

example : (celsiusToKelvin 30 (by norm_num)).toReal -
    (celsiusToKelvin 20 (by norm_num)).toReal = 10 := by
  rw [celsiusToKelvin_sub_celsiusToKelvin]
  norm_num

example (tC : ℝ) (h : -273.15 ≤ tC) :
    kelvinToCelsius (celsiusToKelvin tC h) = tC :=
  kelvinToCelsius_celsiusToKelvin tC h

example (T : Temperature) :
    celsiusToKelvin (kelvinToCelsius T)
      (by have h : 0 ≤ T.toReal := T.val.coe_nonneg
          unfold kelvinToCelsius; linarith) = T :=
  celsiusToKelvin_kelvinToCelsius T

-- Negative Celsius readings above absolute zero are valid.
example : (celsiusToKelvin (-10) (by norm_num)).toReal = 263.15 := by
  change (-10 : ℝ) + 273.15 = 263.15
  norm_num

-- Absolute zero converts without clamping, but cannot supply the factor's proof.
example : (celsiusToKelvin (-273.15) (by norm_num)).toReal = 0 := by
  change (-273.15 : ℝ) + 273.15 = 0
  norm_num

example (h : 0 < (celsiusToKelvin (-273.15) (by norm_num)).toReal) : False := by
  change (0 : ℝ) < -273.15 + 273.15 at h
  norm_num at h

-- A reading below absolute zero cannot supply the conversion's proof.
example (h : (-273.15 : ℝ) ≤ -274) : False := by
  norm_num at h

-- The physical happy path: tagged E/kB and the converted absolute temperature.
example : boltzmannFactor ⟨1000⟩ (celsiusToKelvin 25 (by norm_num))
    (by change (0 : ℝ) < 25 + 273.15; norm_num) =
      Real.exp (-1000 / 298.15) := by
  change Real.exp (-((1000 : ℝ) / (25 + 273.15))) = _
  congr 1
  norm_num

-- Zero energy is valid; zero absolute temperature is not.
example (T : Temperature) (hT : 0 < T.toReal) :
    boltzmannFactor ⟨0⟩ T hT = 1 := by
  change Real.exp (-((0 : ℝ) / T.toReal)) = 1
  simp

-- The energy input is signed: negative relative energies are not truncated.
example : boltzmannFactor ⟨-1000⟩ (Temperature.ofRealNonneg 25 (by norm_num))
    (by change (0 : ℝ) < 25; norm_num) = Real.exp 40 := by
  change Real.exp (-((-1000 : ℝ) / 25)) = _
  congr 1
  norm_num

-- Raw positive Celsius reals cannot be passed as the temperature argument.
example (E : WithDim (Dimension.single ISQDimensionBase.temperature) ℝ)
    (tC : ℝ) (htC : 0 < tC) :
    boltzmannFactor E (Temperature.ofRealNonneg tC htC.le) htC =
      Real.exp (-(E.val / tC)) := by
  fail_if_success have bad : ℝ := boltzmannFactor E tC htC
  rfl

-- Raw energy numbers and quantities with other dimensions are also rejected.
example (T : Temperature) (hT : 0 < T.toReal) (E : ℝ)
    (_p : WithDim pressure ℝ) (_t : WithDim time ℝ) :
    boltzmannFactor ⟨E⟩ T hT = Real.exp (-(E / T.toReal)) := by
  fail_if_success have bad : ℝ := boltzmannFactor E T hT
  fail_if_success have bad : ℝ := boltzmannFactor _p T hT
  fail_if_success have bad : ℝ := boltzmannFactor _t T hT
  rfl

-- The original raw-numeral call from the review must not elaborate.
example : (celsiusToKelvin 0 (by norm_num)).toReal = 273.15 := by
  have _h25 : (0 : ℝ) < 25 := by norm_num
  fail_if_success have bad : ℝ := boltzmannFactor 1000 25 _h25
  change (0 : ℝ) + 273.15 = 273.15
  ring

-- Misinterpreting Celsius requires an explicit absolute-temperature constructor.
example : boltzmannFactor ⟨1000⟩ (Temperature.ofRealNonneg 25 (by norm_num))
    (by change (0 : ℝ) < 25; norm_num) <
      boltzmannFactor ⟨1000⟩ (celsiusToKelvin 25 (by norm_num))
        (by change (0 : ℝ) < 25 + 273.15; norm_num) :=
  boltzmannFactor_lt_boltzmannFactor_celsiusToKelvin (by norm_num) (by norm_num)

end PhyslibExtTest.Chemistry.QuantityCalculus

#print axioms Chemistry.QuantityCalculus.baseOfFin
#print axioms Chemistry.QuantityCalculus.finOfISQ
#print axioms Chemistry.QuantityCalculus.finOfISQ_baseOfFin
#print axioms Chemistry.QuantityCalculus.baseOfFin_finOfISQ
#print axioms Chemistry.QuantityCalculus.exponentVector
#print axioms Chemistry.QuantityCalculus.dimensionOfVector
#print axioms Chemistry.QuantityCalculus.dimensionOfVector_exponentVector
#print axioms Chemistry.QuantityCalculus.exponentVector_dimensionOfVector
#print axioms Chemistry.QuantityCalculus.exponentVector_injective
#print axioms Chemistry.QuantityCalculus.exponentVector_one
#print axioms Chemistry.QuantityCalculus.exponentVector_mul
#print axioms Chemistry.QuantityCalculus.exponentVector_div
#print axioms Chemistry.QuantityCalculus.exponentVector_inv
#print axioms Chemistry.QuantityCalculus.exponentVector_pow
#print axioms Chemistry.QuantityCalculus.exponentVector_single
#print axioms Chemistry.QuantityCalculus.length
#print axioms Chemistry.QuantityCalculus.mass
#print axioms Chemistry.QuantityCalculus.time
#print axioms Chemistry.QuantityCalculus.amount
#print axioms Chemistry.QuantityCalculus.concentration
#print axioms Chemistry.QuantityCalculus.molarMass
#print axioms Chemistry.QuantityCalculus.chemicalPotential
#print axioms Chemistry.QuantityCalculus.diffusivity
#print axioms Chemistry.QuantityCalculus.pressure
#print axioms Chemistry.QuantityCalculus.IsDimensionless
#print axioms Chemistry.QuantityCalculus.isDimensionless_iff
#print axioms Chemistry.QuantityCalculus.length_eq
#print axioms Chemistry.QuantityCalculus.mass_eq
#print axioms Chemistry.QuantityCalculus.time_eq
#print axioms Chemistry.QuantityCalculus.amount_eq
#print axioms Chemistry.QuantityCalculus.concentration_eq
#print axioms Chemistry.QuantityCalculus.molarMass_eq
#print axioms Chemistry.QuantityCalculus.chemicalPotential_eq
#print axioms Chemistry.QuantityCalculus.diffusivity_eq
#print axioms Chemistry.QuantityCalculus.pressure_eq
#print axioms Chemistry.QuantityCalculus.pressure_div_concentration
#print axioms Chemistry.QuantityCalculus.unitFactor
#print axioms Chemistry.QuantityCalculus.rescale
#print axioms Chemistry.QuantityCalculus.unitFactor_eq_prod
#print axioms Chemistry.QuantityCalculus.unitFactor_pos
#print axioms Chemistry.QuantityCalculus.unitFactor_one
#print axioms Chemistry.QuantityCalculus.unitFactor_mul
#print axioms Chemistry.QuantityCalculus.unitFactor_div
#print axioms Chemistry.QuantityCalculus.unitFactor_pow
#print axioms Chemistry.QuantityCalculus.rescale_pos
#print axioms Chemistry.QuantityCalculus.rescale_of_isDimensionless
#print axioms Chemistry.QuantityCalculus.rescale_div_rescale
#print axioms Chemistry.QuantityCalculus.rescale_div_rescale_same
#print axioms Chemistry.QuantityCalculus.rescale_self
#print axioms Chemistry.QuantityCalculus.rescale_transitive
#print axioms Chemistry.QuantityCalculus.SameDimension
#print axioms Chemistry.QuantityCalculus.isDimensionless_div_iff
#print axioms Chemistry.QuantityCalculus.logRatio
#print axioms Chemistry.QuantityCalculus.logRatio_eq_log_sub_log
#print axioms Chemistry.QuantityCalculus.logRatio_self
#print axioms Chemistry.QuantityCalculus.logRatio_mul_mul
#print axioms Chemistry.QuantityCalculus.logRatio_mul_left
#print axioms Chemistry.QuantityCalculus.logRatio_rescale
#print axioms Chemistry.QuantityCalculus.finrank_ker_add_finrank_range
#print axioms Chemistry.QuantityCalculus.mem_ker_mulVecLin_iff
#print axioms Chemistry.QuantityCalculus.finrank_ker_mulVecLin
#print axioms Chemistry.QuantityCalculus.sum_smul_transpose_eq_mulVec
#print axioms Chemistry.QuantityCalculus.dimensionOfVector_zero
#print axioms Chemistry.QuantityCalculus.isDimensionless_mulVec_iff
#print axioms Chemistry.QuantityCalculus.celsiusToKelvin
#print axioms Chemistry.QuantityCalculus.kelvinToCelsius
#print axioms Chemistry.QuantityCalculus.kelvinToCelsius_celsiusToKelvin
#print axioms Chemistry.QuantityCalculus.celsiusToKelvin_kelvinToCelsius
#print axioms Chemistry.QuantityCalculus.celsiusToKelvin_sub_celsiusToKelvin
#print axioms Chemistry.QuantityCalculus.celsiusToKelvin_ne_self
#print axioms Chemistry.QuantityCalculus.boltzmannFactor
#print axioms Chemistry.QuantityCalculus.boltzmannFactor_lt_boltzmannFactor_celsiusToKelvin
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.decimetreScaleScale
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.decimetreScaleScale_pos
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.decimetreScale
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.decimetreScale_scale_apply
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.metreScale_scale_apply
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.metreScale
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.unitFactor_decimetreScale_length
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.unitFactor_decimetreScale_amount
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.rescale_decimetreToMetre_concentration
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.fourierMatrix
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.fourierExponents
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.fourierMatrix_mulVecLin_surjective
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.fourierMatrix_rank
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.finrank_ker_fourierMatrix
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.fourierISQMatrix
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.fourierExponents_mem_ker_fourierISQMatrix
