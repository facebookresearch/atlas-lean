/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Chemistry.QuantityCalculus

/-!
# Tests for `PhyslibExt.Chemistry.QuantityCalculus`

* Quantity kinds: the exponents of concentration and molar mass; concentration is not
  dimensionless; a concentration of `0.01 mol/L` is `10 mol/m³`, and its raw logarithm changes
  with the unit while `logRatio` does not.
* `logRatio`: with `c = 0.01` and `c° = 1`, `logRatio c c°` is `Real.log 0.01`; the logarithm of
  the ratio of equal values is `0`; the ratio `c / c°` of two concentrations is dimensionless,
  and the ratio of a concentration to a molar mass is not.
* Dimensionless groups: the exponent matrix of diffusivity, length and time over the rows length
  and time has rank `2` and a one-dimensional kernel containing the exponents `(1, -2, 1)` of the
  Fourier number `D t / L²`, which is dimensionless over the seven ISQ base quantities.
* Celsius: `25 °C` is `298.15 K`, not `25 K`; for `E = 1000 K` the Boltzmann factor at the Celsius
  reading `25` is `exp (-40)`, strictly smaller than `exp (-1000 / 298.15)` at `298.15 K`.
-/

@[expose] public section

namespace PhyslibExtTest.Chemistry.QuantityCalculus

open Matrix _root_.Chemistry.QuantityCalculus

/-! ## A. Quantity kinds and changes of units -/

-- Concentration has exponent `1` at amount of substance and `-3` at length.
example : concentration 5 = 1 ∧ concentration 0 = -3 := by
  simp [concentration_eq]

-- Molar mass has exponent `1` at mass and `-1` at amount of substance.
example : molarMass 1 = 1 ∧ molarMass 5 = -1 := by
  simp [molarMass_eq]

-- Concentration is not dimensionless.
example : ¬ IsDimensionless concentration := by
  intro h
  have h5 := congrFun (isDimensionless_iff.mp h) 5
  simp [concentration_eq] at h5

/-- The change of units from the decimetre to the metre: one decimetre is `1 / 10` metre, and
the other base units are kept. -/
noncomputable def decimetreToMetre : Fin 7 → ℝ := ![1 / 10, 1, 1, 1, 1, 1, 1]

/-- The factors of the change from the decimetre to the metre are positive. -/
lemma decimetreToMetre_pos : ∀ i, 0 < decimetreToMetre i := by
  intro i
  fin_cases i <;> norm_num [decimetreToMetre]

/-- A concentration of `0.01 mol/L = 0.01 mol/dm³` is `10 mol/m³`. -/
lemma rescale_decimetreToMetre_concentration :
    rescale decimetreToMetre concentration 0.01 = 10 := by
  norm_num [rescale, unitFactor, concentration_eq, decimetreToMetre, Fin.prod_univ_succ]

-- The raw logarithm of the numerical value of a concentration depends on the unit.
example : Real.log (rescale decimetreToMetre concentration 0.01) ≠ Real.log 0.01 := by
  rw [rescale_decimetreToMetre_concentration]
  exact (Real.log_lt_log (by norm_num) (by norm_num)).ne'

-- The logarithm of the ratio of two concentrations does not.
example : logRatio (rescale decimetreToMetre concentration 0.01)
    (rescale decimetreToMetre concentration 1)
    (rescale_pos decimetreToMetre_pos concentration (by norm_num))
    (rescale_pos decimetreToMetre_pos concentration one_pos) =
    logRatio 0.01 1 (by norm_num) one_pos :=
  logRatio_rescale decimetreToMetre_pos concentration (by norm_num) one_pos

-- A ratio of two values of the same kind is unchanged by the change of units.
example : rescale decimetreToMetre pressure 3 / rescale decimetreToMetre pressure 2 = 3 / 2 :=
  rescale_div_rescale_same decimetreToMetre_pos pressure 3 2

-- Converting to the new units and back recovers the value.
example : rescale decimetreToMetre⁻¹ concentration
    (rescale decimetreToMetre concentration 0.01) = 0.01 :=
  rescale_inv_rescale decimetreToMetre_pos concentration 0.01

/-! ## B. Logarithms of ratios -/

-- `ln (c / c°)` with `c = 0.01` and `c° = 1`.
example : logRatio 0.01 1 (by norm_num) one_pos = Real.log 0.01 := by
  simp [logRatio]

-- The logarithm of the ratio of equal values is `0`.
example : logRatio 0.01 0.01 (by norm_num) (by norm_num) = 0 :=
  logRatio_self _

example (x : ℝ) (hx : 0 < x) : logRatio x x hx hx = 0 :=
  logRatio_self hx

-- `ln (c / c°) = ln c - ln c°`.
example : logRatio 0.01 1 (by norm_num) one_pos = Real.log 0.01 - Real.log 1 :=
  logRatio_eq_log_sub_log _ _

-- The ratio `c / c°` of two concentrations is dimensionless.
example : IsDimensionless (concentration - concentration) :=
  isDimensionless_sub_iff.mpr rfl

-- So is the ratio of `p / c` to a chemical potential.
example : IsDimensionless (pressure - concentration - chemicalPotential) :=
  isDimensionless_sub_iff.mpr pressure_sub_concentration

-- The ratio of a concentration to a molar mass is not.
example : ¬ IsDimensionless (concentration - molarMass) := by
  intro h
  have h1 := congrFun (isDimensionless_sub_iff.mp h) 1
  simp [concentration_eq, molarMass_eq] at h1

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
  Matrix.of fun i j => ![diffusivity, length, time] j i

example : IsDimensionless (fourierISQMatrix *ᵥ fourierExponents) := by
  rw [isDimensionless_iff]
  ext i
  fin_cases i <;> simp [fourierISQMatrix, fourierExponents, diffusivity_eq, length, time, mulVec,
    dotProduct, Fin.sum_univ_succ]

-- The same through the monomial convention: `D¹ L⁻² t¹` has exponent vector
-- `diffusivity - 2 • length + time = 0`.
example : fourierExponents ∈ LinearMap.ker fourierISQMatrix.mulVecLin := by
  rw [← isDimensionless_mulVec_iff, ← sum_smul_transpose_eq_mulVec, isDimensionless_iff,
    Fin.sum_univ_three]
  change (1 : ℚ) • diffusivity + (-2 : ℚ) • length + (1 : ℚ) • time = 0
  rw [diffusivity]
  module

/-! ## D. Celsius temperature -/

example : celsiusToKelvin 25 = 298.15 := by
  norm_num [celsiusToKelvin]

example : celsiusToKelvin 25 ≠ 25 := by
  norm_num [celsiusToKelvin]

example : celsiusToKelvin 25 ≠ 25 :=
  celsiusToKelvin_ne_self 25

example : kelvinToCelsius 298.15 = 25 := by
  norm_num [kelvinToCelsius]

example : celsiusToKelvin 30 - celsiusToKelvin 20 = 10 := by
  rw [celsiusToKelvin_sub_celsiusToKelvin]
  norm_num

-- The Boltzmann factor at the Celsius reading `25` in place of `T`.
example : boltzmannFactor 1000 25 = Real.exp (-40) := by
  norm_num [boltzmannFactor]

-- The Boltzmann factor at the thermodynamic temperature `298.15 K`.
example : boltzmannFactor 1000 (celsiusToKelvin 25) = Real.exp (-1000 / 298.15) := by
  norm_num [boltzmannFactor, celsiusToKelvin]

-- The two differ, by strict monotonicity of `Real.exp`.
example : boltzmannFactor 1000 25 < boltzmannFactor 1000 (celsiusToKelvin 25) := by
  rw [boltzmannFactor, boltzmannFactor, celsiusToKelvin, Real.exp_lt_exp]
  norm_num

example : boltzmannFactor 1000 25 ≠ boltzmannFactor 1000 (celsiusToKelvin 25) :=
  (boltzmannFactor_lt_boltzmannFactor_celsiusToKelvin (by norm_num) (by norm_num)).ne

end PhyslibExtTest.Chemistry.QuantityCalculus

#print axioms Chemistry.QuantityCalculus.ExponentVector
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
#print axioms Chemistry.QuantityCalculus.concentration_eq
#print axioms Chemistry.QuantityCalculus.molarMass_eq
#print axioms Chemistry.QuantityCalculus.chemicalPotential_eq
#print axioms Chemistry.QuantityCalculus.diffusivity_eq
#print axioms Chemistry.QuantityCalculus.pressure_eq
#print axioms Chemistry.QuantityCalculus.pressure_sub_concentration
#print axioms Chemistry.QuantityCalculus.unitFactor
#print axioms Chemistry.QuantityCalculus.rescale
#print axioms Chemistry.QuantityCalculus.unitFactor_pos
#print axioms Chemistry.QuantityCalculus.unitFactor_zero
#print axioms Chemistry.QuantityCalculus.unitFactor_add
#print axioms Chemistry.QuantityCalculus.unitFactor_sub
#print axioms Chemistry.QuantityCalculus.rescale_pos
#print axioms Chemistry.QuantityCalculus.rescale_of_isDimensionless
#print axioms Chemistry.QuantityCalculus.rescale_div_rescale
#print axioms Chemistry.QuantityCalculus.rescale_div_rescale_same
#print axioms Chemistry.QuantityCalculus.rescale_inv_rescale
#print axioms Chemistry.QuantityCalculus.SameDimension
#print axioms Chemistry.QuantityCalculus.isDimensionless_sub_iff
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
#print axioms Chemistry.QuantityCalculus.isDimensionless_mulVec_iff
#print axioms Chemistry.QuantityCalculus.celsiusToKelvin
#print axioms Chemistry.QuantityCalculus.kelvinToCelsius
#print axioms Chemistry.QuantityCalculus.kelvinToCelsius_celsiusToKelvin
#print axioms Chemistry.QuantityCalculus.celsiusToKelvin_kelvinToCelsius
#print axioms Chemistry.QuantityCalculus.celsiusToKelvin_sub_celsiusToKelvin
#print axioms Chemistry.QuantityCalculus.celsiusToKelvin_ne_self
#print axioms Chemistry.QuantityCalculus.boltzmannFactor
#print axioms Chemistry.QuantityCalculus.boltzmannFactor_lt_boltzmannFactor_celsiusToKelvin
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.decimetreToMetre
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.decimetreToMetre_pos
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.rescale_decimetreToMetre_concentration
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.fourierMatrix
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.fourierExponents
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.fourierMatrix_mulVecLin_surjective
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.fourierMatrix_rank
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.finrank_ker_fourierMatrix
#print axioms PhyslibExtTest.Chemistry.QuantityCalculus.fourierISQMatrix
