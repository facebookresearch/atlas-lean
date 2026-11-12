/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Quantity calculus, units and dimensional analysis

Exponent vectors of chemical quantity kinds, unit changes, logarithms of ratios, dimensionless
groups by rank–nullity, and the Celsius scale as an offset of the kelvin scale.

## i. Overview

A physical quantity is a number times a unit. Its dimension is a product of powers of the seven
ISQ base quantities, recorded once as an exponent vector `Fin 7 → ℚ` whose coordinates follow the
order of Physlib's `ISQDimensionBase`: `0` length, `1` mass, `2` time, `3` electric current, `4`
thermodynamic temperature, `5` amount of substance, `6` luminous intensity. A quantity kind is a
named exponent vector. Multiplying quantities adds their exponent vectors, dividing subtracts
them, raising to the power `n` multiplies by `n`, and a quantity is dimensionless when its
exponent vector is zero. Quantities of the same kind have the same exponent vector, but not
conversely: torque and energy share one.

Changes of units are stated on plain real numerical values. `rescale s d x` is the numerical value
of a quantity of kind `d` and numerical value `x` after a change of base units in which one old
unit of the base quantity `i` equals `s i > 0` new units; it multiplies `x` by
`unitFactor s d = ∏ i, s i ^ d i`.

These definitions are the exponent and plain-real form of Physlib's units API. The vector `v`
stands for the `Dimension ISQDimensionBase` whose exponent at the `i`-th constructor of
`ISQDimensionBase` is `v i`, read through `Dimension.Exponent.ringEquivRat`. Under this reading
`+`, `-`, `n •` and `0` are Physlib's `*`, `/`, `^ n` and `1` (`Dimension.mul_exponent`,
`Dimension.div_exponent`, `Dimension.npow_exponent`, `Dimension.one_exponent`), and
`Pi.single i 1` is `Dimension.single` of the `i`-th base quantity. Physlib's change of units is
the homomorphism `UnitScale.dimScale u₁ u₂ : Dimension B →* ℝ≥0`, sending `d` to
`∏ b, (u₁.scale b / u₂.scale b) ^ d.exponent b`, and `SIUnitChoices.dimScale` is its instance
over the ISQ basis. `unitFactor s d` is its value at the dimension with exponent vector `d` when
`s i = u₁.scale b / u₂.scale b` for the `i`-th base quantity `b`, and `unitFactor_zero`,
`unitFactor_add` and `rescale_inv_rescale` are the plain-real forms of `UnitScale.dimScale_one`,
`map_mul`, and `UnitScale.dimScale_transitive` with `UnitScale.dimScale_self`. The canonical type
of dimensioned quantities remains Physlib's `WithDim`, whose unit-scaling lemmas are stated over
`LTMCTDimensionBase`; the projection `Dimension.isqToLTMCT` forgets amount of substance and
luminous intensity, so it is not a reversible conversion and is not used here.

Reuse was checked against Mathlib, Physlib and ATLAS main: Mathlib has no quantity calculus,
ATLAS main has no chemistry or units module, and the Physlib counterparts are those named above.
This module adds no second quantity algebra, imports only Mathlib, and depends on no other ATLAS
module, so its correspondence with Physlib is stated here rather than proved.

`Real.log` and `Real.exp` are total functions on `ℝ` (for instance `Real.log 0 = 0`); the
physical API enforces their domain through positivity and the ratio form. The only logarithm
defined here is `logRatio x x₀`, which takes two values together with proofs that both are
positive, and the only exponential is `boltzmannFactor`, whose argument is a ratio of
temperatures; `unitFactor` raises the dimensionless unit ratios `s i` to rational powers. A
logarithm `ln c` of a dimensioned value `c` such as a concentration is rejected because there is
no API entry point for it: no declaration here takes the logarithm or exponential of a single
dimensioned value. The logarithm `ln (c / c°)` is accepted as `logRatio c c°`, with `c°` a
positive standard-state value of the same kind. That both values have the same kind, and hence
the same dimension (`SameDimension`), is a documented precondition: `logRatio` takes no exponent
vectors. `logRatio_rescale` takes both values of one kind `d` and shows that the result does not
depend on the units.

The exponent assignments of the quantity kinds and the Celsius offset are definitions. The
dimension identities, rank–nullity, the algebra of `logRatio` and the agreement of Celsius
differences are mathematical consequences. The domain rule for logarithms and exponentials is an
API discipline, not an empirical law.

## ii. Key results

- `ExponentVector` : exponent vectors of ISQ quantity kinds.
- `concentration_eq`, `molarMass_eq`, `chemicalPotential_eq`, `diffusivity_eq`, `pressure_eq` :
  the exponents of the chemical quantity kinds.
- `unitFactor_add` : the unit factor of a product is the product of the unit factors.
- `rescale_of_isDimensionless`, `rescale_div_rescale_same` : a change of units multiplies a
  dimensionless value by `1`, so the ratio of two values of the same kind does not depend on the
  units.
- `rescale_inv_rescale` : converting a value to other units and back recovers it.
- `isDimensionless_sub_iff` : a ratio is dimensionless exactly when both quantities have the same
  dimension.
- `logRatio_eq_log_sub_log`, `logRatio_self`, `logRatio_mul_mul`, `logRatio_mul_left`,
  `logRatio_rescale` : the algebra of logarithms of ratios, and their independence of the units.
- `finrank_ker_add_finrank_range` : rank–nullity for an exponent matrix.
- `mem_ker_mulVecLin_iff`, `isDimensionless_mulVec_iff` : kernel vectors of an exponent matrix
  are the exponents of dimensionless monomials.
- `kelvinToCelsius_celsiusToKelvin`, `celsiusToKelvin_kelvinToCelsius` : the Celsius and kelvin
  conversions are inverse.
- `celsiusToKelvin_sub_celsiusToKelvin`, `celsiusToKelvin_ne_self` : Celsius and kelvin
  differences agree, values do not.
- `boltzmannFactor_lt_boltzmannFactor_celsiusToKelvin` : a Celsius reading in place of the
  thermodynamic temperature changes the Boltzmann factor.

## iii. Table of contents

- A. Quantity kinds and changes of units
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

/-! ## A. Quantity kinds and changes of units -/

/-- The exponent vector of an ISQ quantity kind. Coordinate `i` is the exponent of the `i`-th ISQ
base quantity in the order of Physlib's `ISQDimensionBase`: `0` length, `1` mass, `2` time, `3`
electric current, `4` thermodynamic temperature, `5` amount of substance, `6` luminous intensity.
Multiplication of quantities adds exponent vectors and division subtracts them. -/
abbrev ExponentVector : Type := Fin 7 → ℚ

/-- The base quantity kind length, `L`. -/
def length : ExponentVector := Pi.single 0 1

/-- The base quantity kind mass, `M`. -/
def mass : ExponentVector := Pi.single 1 1

/-- The base quantity kind time, `T`. -/
def time : ExponentVector := Pi.single 2 1

/-- The base quantity kind amount of substance, `N`. -/
def amount : ExponentVector := Pi.single 5 1

/-- Amount concentration, amount of substance per volume: `N / L³`. -/
def concentration : ExponentVector := amount - 3 • length

/-- Molar mass, mass per amount of substance: `M / N`. -/
def molarMass : ExponentVector := mass - amount

/-- Chemical potential, a molar energy: `M L² / (T² N)`. -/
def chemicalPotential : ExponentVector := mass + 2 • length - (2 • time + amount)

/-- Diffusivity, the diffusion coefficient: `L² / T`. -/
def diffusivity : ExponentVector := 2 • length - time

/-- Pressure, and mechanical stress: `M / (L T²)`. -/
def pressure : ExponentVector := mass - (length + 2 • time)

/-- A quantity kind is dimensionless when its exponent vector is zero. -/
def IsDimensionless (d : ExponentVector) : Prop := d = 0

/-- A quantity kind is dimensionless exactly when its exponent vector is zero. -/
lemma isDimensionless_iff {d : ExponentVector} : IsDimensionless d ↔ d = 0 :=
  Iff.rfl

/-- Concentration has exponent `-3` at length and `1` at amount of substance, and `0` elsewhere. -/
lemma concentration_eq : concentration = ![-3, 0, 0, 0, 0, 1, 0] := by
  funext i
  fin_cases i <;> simp [concentration, amount, length]

/-- Molar mass has exponent `1` at mass and `-1` at amount of substance, and `0` elsewhere. -/
lemma molarMass_eq : molarMass = ![0, 1, 0, 0, 0, -1, 0] := by
  funext i
  fin_cases i <;> simp [molarMass, mass, amount]

/-- Chemical potential has exponents `2` at length, `1` at mass, `-2` at time and `-1` at amount
of substance, and `0` elsewhere. -/
lemma chemicalPotential_eq : chemicalPotential = ![2, 1, -2, 0, 0, -1, 0] := by
  funext i
  fin_cases i <;> simp [chemicalPotential, mass, length, time, amount]

/-- Diffusivity has exponents `2` at length and `-1` at time, and `0` elsewhere. -/
lemma diffusivity_eq : diffusivity = ![2, 0, -1, 0, 0, 0, 0] := by
  funext i
  fin_cases i <;> simp [diffusivity, length, time]

/-- Pressure has exponents `-1` at length, `1` at mass and `-2` at time, and `0` elsewhere. -/
lemma pressure_eq : pressure = ![-1, 1, -2, 0, 0, 0, 0] := by
  funext i
  fin_cases i <;> simp [pressure, mass, length, time]

/-- Pressure divided by amount concentration is a molar energy, as in `p = c R T` for an ideal
gas. -/
lemma pressure_sub_concentration : pressure - concentration = chemicalPotential := by
  rw [pressure_eq, concentration_eq, chemicalPotential_eq]
  funext i
  fin_cases i <;> norm_num

/-- The factor `∏ i, s i ^ d i` by which the numerical value of a quantity of kind `d` is
multiplied under a change of base units in which one old unit of the base quantity `i` equals
`s i` new units. Each `s i` is a ratio of two units of the same kind, a dimensionless number. -/
noncomputable def unitFactor (s : Fin 7 → ℝ) (d : ExponentVector) : ℝ :=
  ∏ i, s i ^ (d i : ℝ)

/-- The numerical value in the new units, `unitFactor s d * x`, of a quantity of kind `d` with
numerical value `x` in the old units. The kind `d` is unchanged. -/
noncomputable def rescale (s : Fin 7 → ℝ) (d : ExponentVector) (x : ℝ) : ℝ :=
  unitFactor s d * x

/-- Positive base-unit factors give a positive unit factor. -/
lemma unitFactor_pos {s : Fin 7 → ℝ} (hs : ∀ i, 0 < s i) (d : ExponentVector) :
    0 < unitFactor s d :=
  Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hs i) _

/-- A dimensionless kind has unit factor `1`. -/
lemma unitFactor_zero (s : Fin 7 → ℝ) : unitFactor s 0 = 1 := by
  simp [unitFactor]

/-- The unit factor of a product of quantities is the product of their unit factors. -/
lemma unitFactor_add {s : Fin 7 → ℝ} (hs : ∀ i, 0 < s i) (d₁ d₂ : ExponentVector) :
    unitFactor s (d₁ + d₂) = unitFactor s d₁ * unitFactor s d₂ := by
  simp only [unitFactor, Pi.add_apply, Rat.cast_add, Real.rpow_add (hs _),
    Finset.prod_mul_distrib]

/-- The unit factor of a quotient of quantities is the quotient of their unit factors. -/
lemma unitFactor_sub {s : Fin 7 → ℝ} (hs : ∀ i, 0 < s i) (d₁ d₂ : ExponentVector) :
    unitFactor s (d₁ - d₂) = unitFactor s d₁ / unitFactor s d₂ := by
  simp only [unitFactor, Pi.sub_apply, Rat.cast_sub, Real.rpow_sub (hs _),
    Finset.prod_div_distrib]

/-- A change of units sends positive values to positive values. -/
lemma rescale_pos {s : Fin 7 → ℝ} (hs : ∀ i, 0 < s i) (d : ExponentVector) {x : ℝ}
    (hx : 0 < x) : 0 < rescale s d x :=
  mul_pos (unitFactor_pos hs d) hx

/-- A change of units multiplies a dimensionless value by `1`. -/
lemma rescale_of_isDimensionless (s : Fin 7 → ℝ) {d : ExponentVector} (hd : IsDimensionless d)
    (x : ℝ) : rescale s d x = x := by
  obtain rfl := isDimensionless_iff.mp hd
  rw [rescale, unitFactor_zero, one_mul]

/-- After a change of units, the ratio of two values transforms with the exponent vector of the
ratio. -/
lemma rescale_div_rescale {s : Fin 7 → ℝ} (hs : ∀ i, 0 < s i) (d₁ d₂ : ExponentVector)
    (x y : ℝ) : rescale s d₁ x / rescale s d₂ y = rescale s (d₁ - d₂) (x / y) := by
  rw [rescale, rescale, rescale, unitFactor_sub hs, mul_div_mul_comm]

/-- The ratio of two values of the same kind does not depend on the units. -/
lemma rescale_div_rescale_same {s : Fin 7 → ℝ} (hs : ∀ i, 0 < s i) (d : ExponentVector)
    (x y : ℝ) : rescale s d x / rescale s d y = x / y := by
  rw [rescale_div_rescale hs, rescale_of_isDimensionless s (isDimensionless_iff.mpr (sub_self d))]

/-- Converting a value to new units with the factors `s` and back with the inverse factors `s⁻¹`
recovers it. -/
lemma rescale_inv_rescale {s : Fin 7 → ℝ} (hs : ∀ i, 0 < s i) (d : ExponentVector) (x : ℝ) :
    rescale s⁻¹ d (rescale s d x) = x := by
  have h : unitFactor s⁻¹ d = (unitFactor s d)⁻¹ := by
    simp only [unitFactor, Pi.inv_apply, Real.inv_rpow (hs _).le, Finset.prod_inv_distrib]
  rw [rescale, rescale, h, inv_mul_cancel_left₀ (unitFactor_pos hs d).ne']

/-! ## B. Logarithms of ratios -/

/-- Two quantity kinds have the same dimension when their exponent vectors are equal, as
quantities of the same kind do. A value divided by a value of the same dimension is
dimensionless (`isDimensionless_sub_iff`). -/
def SameDimension (d₁ d₂ : ExponentVector) : Prop := d₁ = d₂

/-- The ratio of two quantities is dimensionless exactly when they have the same dimension. -/
lemma isDimensionless_sub_iff {d₁ d₂ : ExponentVector} :
    IsDimensionless (d₁ - d₂) ↔ SameDimension d₁ d₂ :=
  sub_eq_zero

/-- The natural logarithm `ln (x / x₀)` of the ratio of a positive value `x` to a positive
reference value `x₀` of the same kind, such as `ln (c / c°)` for a concentration `c` and a
standard concentration `c°`. Only ratios of two positive values are accepted, so there is no
logarithm of a single dimensioned value; that `x` and `x₀` have the same kind, and so the same
dimension (`SameDimension`), is a precondition on the caller. -/
noncomputable def logRatio (x x₀ : ℝ) (_hx : 0 < x) (_hx₀ : 0 < x₀) : ℝ :=
  Real.log (x / x₀)

/-- The logarithm of a ratio is the difference of the logarithms. -/
lemma logRatio_eq_log_sub_log {x x₀ : ℝ} (hx : 0 < x) (hx₀ : 0 < x₀) :
    logRatio x x₀ hx hx₀ = Real.log x - Real.log x₀ :=
  Real.log_div hx.ne' hx₀.ne'

/-- The logarithm of the ratio of a value to itself is `0`. -/
lemma logRatio_self {x : ℝ} (hx : 0 < x) : logRatio x x hx hx = 0 := by
  rw [logRatio, div_self hx.ne', Real.log_one]

/-- The logarithm of a ratio of products splits into the sum of the logarithms of the ratios. -/
lemma logRatio_mul_mul {x x₀ y y₀ : ℝ} (hx : 0 < x) (hx₀ : 0 < x₀) (hy : 0 < y)
    (hy₀ : 0 < y₀) :
    logRatio (x * y) (x₀ * y₀) (mul_pos hx hy) (mul_pos hx₀ hy₀) =
      logRatio x x₀ hx hx₀ + logRatio y y₀ hy hy₀ := by
  rw [logRatio, logRatio, logRatio, ← div_mul_div_comm,
    Real.log_mul (div_pos hx hx₀).ne' (div_pos hy hy₀).ne']

/-- The logarithm of a ratio is unchanged when both values are multiplied by the same positive
factor. -/
lemma logRatio_mul_left {k x x₀ : ℝ} (hk : 0 < k) (hx : 0 < x) (hx₀ : 0 < x₀) :
    logRatio (k * x) (k * x₀) (mul_pos hk hx) (mul_pos hk hx₀) = logRatio x x₀ hx hx₀ := by
  rw [logRatio, logRatio, mul_div_mul_left x x₀ hk.ne']

/-- The logarithm of the ratio of two values of the same kind does not depend on the units. -/
lemma logRatio_rescale {s : Fin 7 → ℝ} (hs : ∀ i, 0 < s i) (d : ExponentVector) {x x₀ : ℝ}
    (hx : 0 < x) (hx₀ : 0 < x₀) :
    logRatio (rescale s d x) (rescale s d x₀) (rescale_pos hs d hx) (rescale_pos hs d hx₀) =
      logRatio x x₀ hx hx₀ :=
  logRatio_mul_left (unitFactor_pos hs d) hx hx₀

/-! ## C. Dimensionless groups

Let the columns of an exponent matrix `D : Matrix (Fin m) (Fin n) ℚ` be the exponent vectors of
quantities `q 0, …, q (n - 1)` over `m` base quantities. With the exponent convention fixed above,
the monomial `∏ j, q j ^ v j` has exponent vector `∑ j, v j • Dᵀ j = D *ᵥ v`
(`sum_smul_transpose_eq_mulVec`). The kernel of `D.mulVecLin` therefore consists exactly of the
exponent vectors of dimensionless monomials (`isDimensionless_mulVec_iff`), and a basis of the
kernel gives `n - D.rank` independent dimensionless groups.

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

/-- For an exponent matrix over the ISQ base quantities, `v` is a kernel vector exactly when the
monomial with exponents `v` is dimensionless. -/
lemma isDimensionless_mulVec_iff {n : ℕ} (D : Matrix (Fin 7) (Fin n) ℚ) (v : Fin n → ℚ) :
    IsDimensionless (D *ᵥ v) ↔ v ∈ LinearMap.ker D.mulVecLin :=
  isDimensionless_iff.trans (mem_ker_mulVecLin_iff D v).symm

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
every result here that divides by a temperature assumes that it is positive.
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
likewise take the thermodynamic temperature only, and `T = 0` is excluded: results that divide
by `T` assume `0 < T`. -/
noncomputable def boltzmannFactor (E T : ℝ) : ℝ := Real.exp (-E / T)

/-- For a positive energy `E`, substituting a positive Celsius reading `tC` for the thermodynamic
temperature gives a strictly smaller Boltzmann factor than the temperature `celsiusToKelvin tC`
in kelvin. -/
lemma boltzmannFactor_lt_boltzmannFactor_celsiusToKelvin {E tC : ℝ} (hE : 0 < E)
    (htC : 0 < tC) : boltzmannFactor E tC < boltzmannFactor E (celsiusToKelvin tC) := by
  rw [boltzmannFactor, boltzmannFactor, Real.exp_lt_exp, neg_div, neg_div, neg_lt_neg_iff,
    celsiusToKelvin]
  exact div_lt_div_of_pos_left hE htC (by norm_num)

end Chemistry.QuantityCalculus
