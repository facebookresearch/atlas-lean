/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Physlib.Units.Dimension
public import Physlib.Units.ISQDimensionBase
public import Physlib.Units.ParametricUnits
public import Physlib.Units.WithDim.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Quantity calculus, units and dimensional analysis

ISQ dimensions, unit changes, logarithms of ratios, dimensionless groups by
rank–nullity, and the Celsius scale as an offset of the kelvin scale.

## i. Overview

A physical quantity is a number times a unit. Its dimension is a product of
powers of the seven ISQ base quantities, recorded as a Physlib
`Dimension ISQDimensionBase`. Multiplying quantities multiplies their
dimensions, dividing divides them, raising to the power `n` raises the
dimension to `n`, and a quantity is dimensionless when its dimension is `1`.
Quantities of the same kind have the same dimension, but not conversely:
torque and energy share one.

The base quantities, in the order used by the exponent-vector bridge below,
are length, mass, time, electric current, thermodynamic temperature, amount of
substance and luminous intensity. `exponentVector d` is the `Fin 7 → ℚ`
exponent vector of `d` in that order, and `dimensionOfVector` is its inverse;
the two are proved inverse (`dimensionOfVector_exponentVector`,
`exponentVector_dimensionOfVector`), so the exponent vectors are a tested
bridge to the `Dimension` algebra, not a parallel algebra: every kind below
is a `Dimension ISQDimensionBase`, and every scaling below is a value of
Physlib's `UnitScale.dimScale`.

Changes of units are stated through `UnitScale.dimScale`. For unit choices
`u₁ u₂ : UnitScale ISQDimensionBase`, `unitFactor u₁ u₂ d` is the real value
of `UnitScale.dimScale u₁ u₂ d : ℝ≥0`, the factor by which the numerical
value of a quantity of dimension `d` is multiplied when the unit choice
changes from `u₁` to `u₂`; `rescale u₁ u₂ d x = unitFactor u₁ u₂ d * x` is
the numerical value in the new units. Transitivity and self-scaling are
Physlib's `UnitScale.dimScale_transitive` and `UnitScale.dimScale_self`.

`Real.log` and `Real.exp` are total functions on `ℝ` (for instance
`Real.log 0 = 0`); the physical API enforces their domain through positivity
and the ratio form. The only logarithm defined here is `logRatio x x₀`, which
takes two values of the same dimension `d`, as `WithDim d ℝ` values, together
with proofs that both are positive, and the only exponential is
`boltzmannFactor`, whose temperature argument carries a proof that it is
positive. A logarithm `ln c` of a dimensioned value `c` such as a
concentration is rejected because there is no API entry point for it: no
declaration here takes the logarithm or exponential of a single dimensioned
value. The logarithm `ln (c / c°)` is accepted as `logRatio c c°`, with `c°`
a positive standard-state value of the same dimension. `logRatio_rescale`
shows that the result does not depend on the units.

The dimension assignments of the quantity kinds and the Celsius offset are
definitions. The dimension identities, rank–nullity, the algebra of
`logRatio` and the agreement of Celsius differences are mathematical
consequences. The domain rule for logarithms and exponentials is an API
discipline, not an empirical law.

## ii. Key results

- `exponentVector`, `dimensionOfVector` : the tested bridge between
  `Dimension ISQDimensionBase` and its `Fin 7 → ℚ` exponent vector.
- `concentration_eq`, `molarMass_eq`, `chemicalPotential_eq`, `diffusivity_eq`,
  `pressure_eq` : the exponents of the chemical quantity kinds.
- `unitFactor_mul`, `unitFactor_div` : the unit factor of a product, resp.
  quotient, of quantities is the product, resp. quotient, of the unit factors.
- `rescale_of_isDimensionless`, `rescale_div_rescale_same` : a change of units
  multiplies a dimensionless value by `1`, so the ratio of two values of the
  same dimension does not depend on the units.
- `rescale_transitive`, `rescale_self` : converting a value to other units and
  back recovers it.
- `isDimensionless_div_iff` : a ratio is dimensionless exactly when both
  quantities have the same dimension.
- `logRatio_eq_log_sub_log`, `logRatio_self`, `logRatio_mul_mul`,
  `logRatio_mul_left`, `logRatio_rescale` : the algebra of logarithms of
  ratios, and their independence of the units.
- `finrank_ker_add_finrank_range` : rank–nullity for an exponent matrix.
- `mem_ker_mulVecLin_iff`, `isDimensionless_mulVec_iff` : kernel vectors of an
  exponent matrix are the exponents of dimensionless monomials.
- `kelvinToCelsius_celsiusToKelvin`, `celsiusToKelvin_kelvinToCelsius` : the
  Celsius and kelvin conversions are inverse.
- `celsiusToKelvin_sub_celsiusToKelvin`, `celsiusToKelvin_ne_self` : Celsius
  and kelvin differences agree, values do not.
- `boltzmannFactor_lt_boltzmannFactor_celsiusToKelvin` : a Celsius reading in
  place of the thermodynamic temperature changes the Boltzmann factor.

## iii. Table of contents

- A. Quantity kinds, exponent vectors and changes of units
- B. Logarithms of ratios
- C. Dimensionless groups
- D. Celsius temperature

## iv. References

- IUPAC, *Quantities, Units and Symbols in Physical Chemistry* (the Green Book), 4th edition,
  abridged version, C. M. A. Brett et al., Royal Society of Chemistry, ISBN 978-1-83916-150-6:
  quantity calculus, the ISQ base quantities, dimensionless arguments of logarithms and
  exponentials, standard states.
- OpenStax, *Chemistry 2e*, Chapter 1: measurements, unit conversions and dimensional analysis.
- `Physlib.Units.Dimension`, `Physlib.Units.ISQDimensionBase`, `Physlib.Units.ParametricUnits`,
  `Physlib.Units.SIUnitChoices`, `Physlib.Units.ISQBridge`, `Physlib.Units.WithDim.Basic` and
  `Physlib.Thermodynamics.Temperature.TemperatureUnits` in
  https://github.com/leanprover-community/physlib at `v4.35.0`.
-/

@[expose] public section

namespace Chemistry.QuantityCalculus

open Matrix
open scoped NNReal

/-! ## A. Quantity kinds, exponent vectors and changes of units -/

/-- The ISQ base quantity at index `i`, in the order length, mass, time,
electric current, thermodynamic temperature, amount of substance, luminous
intensity. -/
def baseOfFin : Fin 7 → ISQDimensionBase :=
  ![.length, .mass, .time, .current, .temperature, .amount, .luminousIntensity]

/-- The index of an ISQ base quantity, inverse to `baseOfFin`. -/
def finOfISQ : ISQDimensionBase → Fin 7
  | .length => 0
  | .mass => 1
  | .time => 2
  | .current => 3
  | .temperature => 4
  | .amount => 5
  | .luminousIntensity => 6

/-- `finOfISQ` is inverse to `baseOfFin`. -/
lemma finOfISQ_baseOfFin (i : Fin 7) : finOfISQ (baseOfFin i) = i := by
  fin_cases i <;> rfl

/-- `baseOfFin` is inverse to `finOfISQ`. -/
lemma baseOfFin_finOfISQ (b : ISQDimensionBase) : baseOfFin (finOfISQ b) = b := by
  cases b <;> rfl

/-- The exponent vector of an ISQ dimension, in the order of `baseOfFin`:
coordinate `i` is the exponent of `baseOfFin i`. -/
def exponentVector (d : Dimension ISQDimensionBase) : Fin 7 → ℚ :=
  fun i => (d.exponent (baseOfFin i) : ℚ)

/-- The ISQ dimension with a given exponent vector, inverse to
`exponentVector`. -/
def dimensionOfVector (v : Fin 7 → ℚ) : Dimension ISQDimensionBase :=
  Dimension.ofFunction fun b => Dimension.Exponent.ofRat (v (finOfISQ b))

/-- `dimensionOfVector` is inverse to `exponentVector`. -/
lemma dimensionOfVector_exponentVector (d : Dimension ISQDimensionBase) :
    dimensionOfVector (exponentVector d) = d := by
  apply Dimension.ext
  intro b
  simp only [dimensionOfVector, exponentVector, Dimension.ofFunction_exponent,
    baseOfFin_finOfISQ]
  obtain ⟨q⟩ := d.exponent b
  rfl

/-- `exponentVector` is inverse to `dimensionOfVector`. -/
lemma exponentVector_dimensionOfVector (v : Fin 7 → ℚ) :
    exponentVector (dimensionOfVector v) = v := by
  funext i
  simp [exponentVector, dimensionOfVector, Dimension.ofFunction_exponent,
    finOfISQ_baseOfFin, Dimension.Exponent.ofRat_toRat]

/-- `exponentVector` is injective: a dimension is determined by its exponents. -/
lemma exponentVector_injective : Function.Injective exponentVector := by
  intro d₁ d₂ h
  rw [← dimensionOfVector_exponentVector d₁, ← dimensionOfVector_exponentVector d₂, h]

/-- The exponent vector of the dimensionless dimension is zero. -/
lemma exponentVector_one : exponentVector (1 : Dimension ISQDimensionBase) = 0 := by
  funext i
  simp [exponentVector]

/-- The exponent vector of a product is the sum of the exponent vectors. -/
lemma exponentVector_mul (d₁ d₂ : Dimension ISQDimensionBase) :
    exponentVector (d₁ * d₂) = exponentVector d₁ + exponentVector d₂ := by
  funext i
  simp [exponentVector, Dimension.mul_exponent]

/-- The exponent vector of a quotient is the difference of the exponent vectors. -/
lemma exponentVector_div (d₁ d₂ : Dimension ISQDimensionBase) :
    exponentVector (d₁ / d₂) = exponentVector d₁ - exponentVector d₂ := by
  funext i
  simp [exponentVector, Dimension.div_exponent]

/-- The exponent vector of an inverse is the negation of the exponent vector. -/
lemma exponentVector_inv (d : Dimension ISQDimensionBase) :
    exponentVector d⁻¹ = -exponentVector d := by
  funext i
  simp [exponentVector, Dimension.inv_exponent]

/-- The exponent vector of a power is the scalar multiple of the exponent vector. -/
lemma exponentVector_pow (d : Dimension ISQDimensionBase) (n : ℕ) :
    exponentVector (d ^ n) = n • exponentVector d := by
  induction n with
  | zero => simp [exponentVector_one]
  | succ n ih => rw [pow_succ, exponentVector_mul, ih, succ_nsmul]

/-- The exponent vector of a base dimension is the corresponding unit vector. -/
lemma exponentVector_single (b : ISQDimensionBase) :
    exponentVector (Dimension.single b) = Pi.single (finOfISQ b) 1 := by
  funext i
  by_cases h : finOfISQ b = i
  · subst h
    simp [exponentVector, baseOfFin_finOfISQ]
  · have hbi : baseOfFin i ≠ b := by
      intro hb
      apply h
      rw [← hb, finOfISQ_baseOfFin]
    have h' : i ≠ finOfISQ b := fun he => h he.symm
    simp [exponentVector, h', hbi, Dimension.single_exponent]

/-- The base quantity kind length, `L`. -/
def length : Dimension ISQDimensionBase := Dimension.single .length

/-- The base quantity kind mass, `M`. -/
def mass : Dimension ISQDimensionBase := Dimension.single .mass

/-- The base quantity kind time, `T`. -/
def time : Dimension ISQDimensionBase := Dimension.single .time

/-- The base quantity kind amount of substance, `N`. -/
def amount : Dimension ISQDimensionBase := Dimension.single .amount

/-- Amount concentration, amount of substance per volume: `N / L³`. -/
def concentration : Dimension ISQDimensionBase := amount / length ^ (3 : ℕ)

/-- Molar mass, mass per amount of substance: `M / N`. -/
def molarMass : Dimension ISQDimensionBase := mass / amount

/-- Chemical potential, a molar energy: `M L² / (T² N)`. -/
def chemicalPotential : Dimension ISQDimensionBase :=
  mass * length ^ (2 : ℕ) / (time ^ (2 : ℕ) * amount)

/-- Diffusivity, the diffusion coefficient: `L² / T`. -/
def diffusivity : Dimension ISQDimensionBase := length ^ (2 : ℕ) / time

/-- Pressure, and mechanical stress: `M / (L T²)`. -/
def pressure : Dimension ISQDimensionBase := mass / (length * time ^ (2 : ℕ))

/-- A quantity kind is dimensionless when its dimension is `1`. -/
def IsDimensionless (d : Dimension ISQDimensionBase) : Prop := d = 1

/-- A quantity kind is dimensionless exactly when its dimension is `1`. -/
lemma isDimensionless_iff {d : Dimension ISQDimensionBase} :
    IsDimensionless d ↔ d = 1 :=
  Iff.rfl

/-- Length has exponent `1` at length and `0` elsewhere. -/
lemma length_eq : exponentVector length = Pi.single 0 1 := by
  simp [length, exponentVector_single, finOfISQ]

/-- Mass has exponent `1` at mass and `0` elsewhere. -/
lemma mass_eq : exponentVector mass = Pi.single 1 1 := by
  simp [mass, exponentVector_single, finOfISQ]

/-- Time has exponent `1` at time and `0` elsewhere. -/
lemma time_eq : exponentVector time = Pi.single 2 1 := by
  simp [time, exponentVector_single, finOfISQ]

/-- Amount of substance has exponent `1` at amount and `0` elsewhere. -/
lemma amount_eq : exponentVector amount = Pi.single 5 1 := by
  simp [amount, exponentVector_single, finOfISQ]

/-- Concentration has exponent `-3` at length and `1` at amount of substance, and `0` elsewhere. -/
lemma concentration_eq : exponentVector concentration = ![-3, 0, 0, 0, 0, 1, 0] := by
  rw [concentration, exponentVector_div, exponentVector_pow, amount_eq, length_eq]
  funext i
  fin_cases i <;> simp

/-- Molar mass has exponent `1` at mass and `-1` at amount of substance, and `0` elsewhere. -/
lemma molarMass_eq : exponentVector molarMass = ![0, 1, 0, 0, 0, -1, 0] := by
  rw [molarMass, exponentVector_div, mass_eq, amount_eq]
  funext i
  fin_cases i <;> simp

/-- Chemical potential has exponents `2` at length, `1` at mass, `-2` at time and `-1` at amount
of substance, and `0` elsewhere. -/
lemma chemicalPotential_eq :
    exponentVector chemicalPotential = ![2, 1, -2, 0, 0, -1, 0] := by
  rw [chemicalPotential, exponentVector_div, exponentVector_mul, exponentVector_mul,
    exponentVector_pow, exponentVector_pow, mass_eq, length_eq, time_eq, amount_eq]
  funext i
  fin_cases i <;> simp

/-- Diffusivity has exponents `2` at length and `-1` at time, and `0` elsewhere. -/
lemma diffusivity_eq : exponentVector diffusivity = ![2, 0, -1, 0, 0, 0, 0] := by
  rw [diffusivity, exponentVector_div, exponentVector_pow, length_eq, time_eq]
  funext i
  fin_cases i <;> simp

/-- Pressure has exponents `-1` at length, `1` at mass and `-2` at time, and `0` elsewhere. -/
lemma pressure_eq : exponentVector pressure = ![-1, 1, -2, 0, 0, 0, 0] := by
  rw [pressure, exponentVector_div, exponentVector_mul, exponentVector_pow, mass_eq, length_eq,
    time_eq]
  funext i
  fin_cases i <;> simp

/-- Pressure divided by amount concentration is a molar energy, as in `p = c R T` for an ideal
gas. -/
lemma pressure_div_concentration : pressure / concentration = chemicalPotential := by
  apply exponentVector_injective
  rw [exponentVector_div, pressure_eq, concentration_eq, chemicalPotential_eq]
  funext i
  fin_cases i
  all_goals simp
  all_goals norm_num

/-- The factor by which the numerical value of a quantity of dimension `d` is multiplied under a
change of unit choices from `u₁` to `u₂`: the real value of Physlib's
`UnitScale.dimScale u₁ u₂ d : ℝ≥0`. -/
noncomputable def unitFactor (u₁ u₂ : UnitScale ISQDimensionBase)
    (d : Dimension ISQDimensionBase) : ℝ :=
  ((UnitScale.dimScale u₁ u₂ d : ℝ≥0) : ℝ)

/-- The numerical value in the new units, `unitFactor u₁ u₂ d * x`, of a quantity of dimension
`d` with numerical value `x` in the old units. The dimension `d` is unchanged. -/
noncomputable def rescale (u₁ u₂ : UnitScale ISQDimensionBase)
    (d : Dimension ISQDimensionBase) (x : ℝ) : ℝ :=
  unitFactor u₁ u₂ d * x

/-- `unitFactor` as an explicit product over the ISQ base quantities, the unfolded form of
`UnitScale.dimScale`. -/
lemma unitFactor_eq_prod (u₁ u₂ : UnitScale ISQDimensionBase)
    (d : Dimension ISQDimensionBase) :
    unitFactor u₁ u₂ d =
      ∏ b, ((u₁.scale b / u₂.scale b : ℝ≥0) : ℝ) ^ ((d.exponent b : ℚ) : ℝ) := by
  simp only [unitFactor, UnitScale.dimScale, MonoidHom.coe_mk, OneHom.coe_mk,
    NNReal.coe_prod, NNReal.coe_rpow]

/-- Positive unit choices give a positive unit factor. -/
lemma unitFactor_pos (u₁ u₂ : UnitScale ISQDimensionBase) (d : Dimension ISQDimensionBase) :
    0 < unitFactor u₁ u₂ d := by
  rw [unitFactor_eq_prod]
  apply Finset.prod_pos
  intro b _
  exact Real.rpow_pos_of_pos
    (NNReal.coe_pos.mpr (div_pos (u₁.scale_pos b) (u₂.scale_pos b))) _

/-- A dimensionless kind has unit factor `1`. -/
lemma unitFactor_one (u₁ u₂ : UnitScale ISQDimensionBase) :
    unitFactor u₁ u₂ 1 = 1 := by
  simp only [unitFactor, map_one, NNReal.coe_one]

/-- The unit factor of a product of quantities is the product of their unit factors. -/
lemma unitFactor_mul (u₁ u₂ : UnitScale ISQDimensionBase)
    (d₁ d₂ : Dimension ISQDimensionBase) :
    unitFactor u₁ u₂ (d₁ * d₂) = unitFactor u₁ u₂ d₁ * unitFactor u₁ u₂ d₂ := by
  simp only [unitFactor, map_mul, NNReal.coe_mul]

/-- The unit factor of a quotient of quantities is the quotient of their unit factors. -/
lemma unitFactor_div (u₁ u₂ : UnitScale ISQDimensionBase)
    (d₁ d₂ : Dimension ISQDimensionBase) :
    unitFactor u₁ u₂ (d₁ / d₂) = unitFactor u₁ u₂ d₁ / unitFactor u₁ u₂ d₂ := by
  have hpos : ∀ b : ISQDimensionBase, 0 < ((u₁.scale b / u₂.scale b : ℝ≥0) : ℝ) :=
    fun b => NNReal.coe_pos.mpr (div_pos (u₁.scale_pos b) (u₂.scale_pos b))
  rw [unitFactor_eq_prod, unitFactor_eq_prod, unitFactor_eq_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro b _
  rw [← Real.rpow_sub (hpos b)]
  congr 1
  simp [Dimension.div_exponent, Dimension.Exponent.coe_sub, Rat.cast_sub]

/-- The unit factor of a power of a quantity is the power of its unit factor. -/
lemma unitFactor_pow (u₁ u₂ : UnitScale ISQDimensionBase)
    (d : Dimension ISQDimensionBase) (n : ℕ) :
    unitFactor u₁ u₂ (d ^ n) = unitFactor u₁ u₂ d ^ n := by
  simp only [unitFactor, map_pow, NNReal.coe_pow]

/-- A change of units sends positive values to positive values. -/
lemma rescale_pos (u₁ u₂ : UnitScale ISQDimensionBase) (d : Dimension ISQDimensionBase)
    {x : ℝ} (hx : 0 < x) : 0 < rescale u₁ u₂ d x :=
  mul_pos (unitFactor_pos u₁ u₂ d) hx

/-- A change of units multiplies a dimensionless value by `1`. -/
lemma rescale_of_isDimensionless (u₁ u₂ : UnitScale ISQDimensionBase)
    {d : Dimension ISQDimensionBase} (hd : IsDimensionless d) (x : ℝ) :
    rescale u₁ u₂ d x = x := by
  obtain rfl := isDimensionless_iff.mp hd
  rw [rescale, unitFactor_one, one_mul]

/-- After a change of units, the ratio of two values transforms with the dimension of the
ratio. -/
lemma rescale_div_rescale (u₁ u₂ : UnitScale ISQDimensionBase)
    (d₁ d₂ : Dimension ISQDimensionBase) (x y : ℝ) :
    rescale u₁ u₂ d₁ x / rescale u₁ u₂ d₂ y = rescale u₁ u₂ (d₁ / d₂) (x / y) := by
  rw [rescale, rescale, rescale, unitFactor_div, mul_div_mul_comm]

/-- The ratio of two values of the same dimension does not depend on the units. -/
lemma rescale_div_rescale_same (u₁ u₂ : UnitScale ISQDimensionBase)
    (d : Dimension ISQDimensionBase) (x y : ℝ) :
    rescale u₁ u₂ d x / rescale u₁ u₂ d y = x / y := by
  have h : d / d = (1 : Dimension ISQDimensionBase) := by simp
  rw [rescale_div_rescale, h,
    rescale_of_isDimensionless u₁ u₂ (isDimensionless_iff.mpr rfl)]

/-- Converting a value to other units and back recovers it: the self-scaling case of
transitivity. -/
lemma rescale_self (u : UnitScale ISQDimensionBase) (d : Dimension ISQDimensionBase)
    (x : ℝ) : rescale u u d x = x := by
  simp only [rescale, unitFactor, UnitScale.dimScale_self, NNReal.coe_one, one_mul]

/-- Converting through an intermediate unit choice is the direct conversion, by
`UnitScale.dimScale_transitive`. -/
lemma rescale_transitive (u₁ u₂ u₃ : UnitScale ISQDimensionBase)
    (d : Dimension ISQDimensionBase) (x : ℝ) :
    rescale u₂ u₃ d (rescale u₁ u₂ d x) = rescale u₁ u₃ d x := by
  have h : unitFactor u₁ u₂ d * unitFactor u₂ u₃ d = unitFactor u₁ u₃ d := by
    simp only [unitFactor, ← NNReal.coe_mul, UnitScale.dimScale_transitive]
  rw [rescale, rescale, rescale, ← mul_assoc,
    mul_comm (unitFactor u₂ u₃ d) (unitFactor u₁ u₂ d), h]

/-! ## B. Logarithms of ratios -/

/-- Two quantity kinds have the same dimension when their dimensions are equal, as quantities of
the same kind do. A value divided by a value of the same dimension is dimensionless
(`isDimensionless_div_iff`). -/
def SameDimension (d₁ d₂ : Dimension ISQDimensionBase) : Prop := d₁ = d₂

/-- The ratio of two quantities is dimensionless exactly when they have the same dimension. -/
lemma isDimensionless_div_iff {d₁ d₂ : Dimension ISQDimensionBase} :
    IsDimensionless (d₁ / d₂) ↔ SameDimension d₁ d₂ := by
  change d₁ / d₂ = 1 ↔ d₁ = d₂
  constructor
  · intro h
    have h2 := congrArg (· * d₂) h
    simpa using h2
  · intro h
    rw [h]
    simp

/-- The natural logarithm `ln (x / x₀)` of the ratio of a positive value `x` to a positive
reference value `x₀` of the same dimension `d`, such as `ln (c / c°)` for a concentration `c`
and a standard concentration `c°`. Only ratios of two positive values of one dimension are
accepted, so there is no logarithm of a single dimensioned value; that `x` and `x₀` have the
same dimension is enforced by their type `WithDim d ℝ`. -/
noncomputable def logRatio {d : Dimension ISQDimensionBase} (x x₀ : WithDim d ℝ)
    (_hx : 0 < x.val) (_hx₀ : 0 < x₀.val) : ℝ :=
  Real.log (x.val / x₀.val)

/-- The logarithm of a ratio is the difference of the logarithms. -/
lemma logRatio_eq_log_sub_log {d : Dimension ISQDimensionBase} {x x₀ : WithDim d ℝ}
    (hx : 0 < x.val) (hx₀ : 0 < x₀.val) :
    logRatio x x₀ hx hx₀ = Real.log x.val - Real.log x₀.val :=
  Real.log_div hx.ne' hx₀.ne'

/-- The logarithm of the ratio of a value to itself is `0`. -/
lemma logRatio_self {d : Dimension ISQDimensionBase} {x : WithDim d ℝ} (hx : 0 < x.val) :
    logRatio x x hx hx = 0 := by
  rw [logRatio, div_self hx.ne', Real.log_one]

/-- The logarithm of a ratio of products splits into the sum of the logarithms of the ratios. -/
lemma logRatio_mul_mul {d₁ d₂ : Dimension ISQDimensionBase}
    {x x₀ : WithDim d₁ ℝ} {y y₀ : WithDim d₂ ℝ}
    (hx : 0 < x.val) (hx₀ : 0 < x₀.val) (hy : 0 < y.val) (hy₀ : 0 < y₀.val) :
    logRatio (x * y) (x₀ * y₀)
        (by rw [WithDim.withDim_hMul_val]; exact mul_pos hx hy)
        (by rw [WithDim.withDim_hMul_val]; exact mul_pos hx₀ hy₀) =
      logRatio x x₀ hx hx₀ + logRatio y y₀ hy hy₀ := by
  simp only [logRatio, WithDim.withDim_hMul_val, ← div_mul_div_comm,
    Real.log_mul (div_pos hx hx₀).ne' (div_pos hy hy₀).ne']

/-- The logarithm of a ratio is unchanged when both values are multiplied by the same positive
factor. -/
lemma logRatio_mul_left {d : Dimension ISQDimensionBase} {x x₀ : WithDim d ℝ} {k : ℝ}
    (hk : 0 < k) (hx : 0 < x.val) (hx₀ : 0 < x₀.val) :
    logRatio (k • x) (k • x₀)
        (by rw [WithDim.real_smul_val, smul_eq_mul]; exact mul_pos hk hx)
        (by rw [WithDim.real_smul_val, smul_eq_mul]; exact mul_pos hk hx₀) =
      logRatio x x₀ hx hx₀ := by
  simp only [logRatio, WithDim.real_smul_val, smul_eq_mul, mul_div_mul_left _ _ hk.ne']

/-- The logarithm of the ratio of two values of the same dimension does not depend on the
units: a change of units multiplies both values by the same positive unit factor. -/
lemma logRatio_rescale (u₁ u₂ : UnitScale ISQDimensionBase)
    {d : Dimension ISQDimensionBase} {x x₀ : WithDim d ℝ}
    (hx : 0 < x.val) (hx₀ : 0 < x₀.val) :
    logRatio ((unitFactor u₁ u₂ d) • x) ((unitFactor u₁ u₂ d) • x₀)
        (by rw [WithDim.real_smul_val, smul_eq_mul]
            exact mul_pos (unitFactor_pos u₁ u₂ d) hx)
        (by rw [WithDim.real_smul_val, smul_eq_mul]
            exact mul_pos (unitFactor_pos u₁ u₂ d) hx₀) =
      logRatio x x₀ hx hx₀ :=
  logRatio_mul_left (unitFactor_pos u₁ u₂ d) hx hx₀

/-! ## C. Dimensionless groups

Let the columns of an exponent matrix `D : Matrix (Fin m) (Fin n) ℚ` be the exponent vectors of
quantities `q 0, …, q (n - 1)` over `m` base quantities, in the `baseOfFin` order when
`m = 7`. With the exponent convention fixed above, the exponent vector of the monomial
`∏ j, q j ^ v j` is `∑ j, v j • Dᵀ j = D *ᵥ v` (`sum_smul_transpose_eq_mulVec`). The kernel
of `D.mulVecLin` therefore consists exactly of the exponent vectors of dimensionless
monomials (`isDimensionless_mulVec_iff`), and a basis of the kernel gives `n - D.rank`
independent dimensionless groups.

Rank–nullity only counts and characterizes these groups. The functional Buckingham π theorem,
that every dimensionally homogeneous relation among the quantities is equivalent to a relation
among a complete set of dimensionless groups, is not proved here.
-/

/-- **Rank–nullity theorem** for an exponent matrix `D` over `n` quantities: the dimension of the
kernel, the space of exponent vectors of dimensionless monomials, plus the rank of `D` is `n`.
This counts the independent dimensionless groups; it is not the functional Buckingham π
theorem. -/
theorem finrank_ker_add_finrank_range {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) :
    Module.finrank ℚ (LinearMap.ker D.mulVecLin) +
      Module.finrank ℚ (LinearMap.range D.mulVecLin) = n := by
  rw [add_comm, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]

/-- A vector lies in the kernel of the exponent matrix `D` exactly when `D *ᵥ v = 0`. -/
lemma mem_ker_mulVecLin_iff {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) (v : Fin n → ℚ) :
    v ∈ LinearMap.ker D.mulVecLin ↔ D *ᵥ v = 0 := by
  rw [LinearMap.mem_ker, mulVecLin_apply]

/-- The number of independent dimensionless groups is the number of quantities minus the rank of
the exponent matrix. -/
lemma finrank_ker_mulVecLin {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) :
    Module.finrank ℚ (LinearMap.ker D.mulVecLin) = n - D.rank := by
  have h := finrank_ker_add_finrank_range D
  rw [← Matrix.rank] at h
  omega

/-- The exponent vector of the monomial `∏ j, q j ^ v j`, computed by adding the exponent vectors
`Dᵀ j` of the factors `q j` scaled by their powers `v j`, is `D *ᵥ v`. -/
lemma sum_smul_transpose_eq_mulVec {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) (v : Fin n → ℚ) :
    ∑ j, v j • Dᵀ j = D *ᵥ v := by
  simp [mulVec_eq_sum, op_smul_eq_smul]

/-- The dimension with exponent vector `0` is the dimensionless dimension `1`. -/
lemma dimensionOfVector_zero : dimensionOfVector 0 = 1 := by
  apply exponentVector_injective
  rw [exponentVector_dimensionOfVector, exponentVector_one]

/-- For an exponent matrix over the ISQ base quantities, `v` is a kernel vector exactly when the
monomial with exponents `v` is dimensionless. -/
lemma isDimensionless_mulVec_iff {n : ℕ} (D : Matrix (Fin 7) (Fin n) ℚ) (v : Fin n → ℚ) :
    IsDimensionless (dimensionOfVector (D *ᵥ v)) ↔ v ∈ LinearMap.ker D.mulVecLin := by
  constructor
  · intro h
    have h2 := congrArg exponentVector (isDimensionless_iff.mp h)
    rw [exponentVector_dimensionOfVector, exponentVector_one] at h2
    exact (mem_ker_mulVecLin_iff D v).mpr h2
  · intro h
    have h2 : D *ᵥ v = 0 := (mem_ker_mulVecLin_iff D v).mp h
    rw [isDimensionless_iff, h2, dimensionOfVector_zero]

/-! ## D. Celsius temperature

The Celsius temperature is the thermodynamic temperature shifted by `273.15`. Physlib's
`Temperature` is an absolute temperature, zero at absolute zero, and its `TemperatureUnit`s are
multiplicative scalings of `TemperatureUnit.kelvin`; its temperature API map lists scales with an
offset zero, such as degrees Celsius, as not yet provided. The Celsius offset is therefore
defined here on real numbers. Differences agree on the two scales, but values do not, so laws
that use the absolute temperature take it in kelvin. The Boltzmann factor `exp (-E / T)` takes
the thermodynamic temperature `T`; Arrhenius factors `exp (-Eₐ / (R T))` and the Nernst
exponential `exp (n F E / (R T))` likewise take the thermodynamic temperature only, never a
Celsius reading. The temperature `T = 0` is excluded wherever the inverse temperature is used:
`boltzmannFactor` takes a proof that its temperature argument is positive.
-/

/-- The thermodynamic temperature in kelvin, `tC + 273.15`, of the Celsius temperature `tC` in
degrees Celsius. -/
def celsiusToKelvin (tC : ℝ) : ℝ := tC + 273.15

/-- The Celsius temperature in degrees Celsius, `tK - 273.15`, of the thermodynamic temperature
`tK` in kelvin. -/
def kelvinToCelsius (tK : ℝ) : ℝ := tK - 273.15

/-- Converting a Celsius temperature to kelvin and back recovers it. -/
lemma kelvinToCelsius_celsiusToKelvin (tC : ℝ) : kelvinToCelsius (celsiusToKelvin tC) = tC :=
  add_sub_cancel_right tC 273.15

/-- Converting a thermodynamic temperature to degrees Celsius and back recovers it. -/
lemma celsiusToKelvin_kelvinToCelsius (tK : ℝ) : celsiusToKelvin (kelvinToCelsius tK) = tK :=
  sub_add_cancel tK 273.15

/-- A temperature difference is the same in degrees Celsius and in kelvin. -/
lemma celsiusToKelvin_sub_celsiusToKelvin (t₁ t₂ : ℝ) :
    celsiusToKelvin t₂ - celsiusToKelvin t₁ = t₂ - t₁ :=
  add_sub_add_right_eq_sub t₂ t₁ 273.15

/-- The kelvin value `tC + 273.15` of a Celsius reading `tC` is never `tC`: a Celsius reading is
not the thermodynamic temperature. -/
lemma celsiusToKelvin_ne_self (tC : ℝ) : celsiusToKelvin tC ≠ tC := by
  norm_num [celsiusToKelvin]

/-- The Boltzmann factor `exp (-E / T)` of a state of energy `E` at the thermodynamic temperature
`T > 0` in kelvin. The energy `E` is given already divided by the Boltzmann constant, so it is in
kelvin and `-E / T` is a dimensionless ratio of temperatures. Arrhenius and Nernst exponentials
likewise take the thermodynamic temperature only, and `T = 0` is excluded by the positivity
proof `hT`: `boltzmannFactor E 0` has no API entry point. -/
noncomputable def boltzmannFactor (E T : ℝ) (_hT : 0 < T) : ℝ := Real.exp (-E / T)

/-- For a positive energy `E`, substituting a positive Celsius reading `tC` for the thermodynamic
temperature gives a strictly smaller Boltzmann factor than the temperature `celsiusToKelvin tC`
in kelvin. -/
lemma boltzmannFactor_lt_boltzmannFactor_celsiusToKelvin {E tC : ℝ} (hE : 0 < E)
    (htC : 0 < tC) :
    boltzmannFactor E tC htC <
      boltzmannFactor E (celsiusToKelvin tC) (by
        have h : 0 < tC + 273.15 := by linarith
        exact h) := by
  rw [boltzmannFactor, boltzmannFactor, Real.exp_lt_exp, neg_div, neg_div, neg_lt_neg_iff,
    celsiusToKelvin]
  exact div_lt_div_of_pos_left hE htC (by norm_num)

end Chemistry.QuantityCalculus
