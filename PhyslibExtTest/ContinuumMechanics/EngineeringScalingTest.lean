/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.ContinuumMechanics.EngineeringScaling

/-!
# Tests for `PhyslibExt.ContinuumMechanics.EngineeringScaling`

* the exponents of the thermal-transport dimensions at all seven ISQ
  base quantities;
* the dimension identities of the Reynolds, Prandtl, Nusselt (and
  Biot), Rayleigh and Froude monomials;
* the coordinate formulas on concrete values: the Reynolds, Mach and
  Froude numbers see only the speed `|U|` and the Rayleigh number only
  `|g|`, `ΔT` keeps its sign, and one `h L` gives different Nusselt and
  Biot numbers against a fluid and a solid conductivity;
* unit invariance at arbitrary scales and the two-scale fixtures;
* a molar heat capacity is not mass-specific, and the unconverted
  molar Prandtl expression is not unit invariant;
* the scaled transport field `ĉ(t̂, x̂) = t̂ + x̂²` with `L = 2`, `U = 3`,
  `C0 = 1`: nonzero physical derivatives, and the second-derivative
  factor `C0 / L²` against the wrong first-power factor `C0 / L`.
-/

@[expose] public section

namespace PhyslibExtTest.ContinuumMechanics.EngineeringScaling

open Dimension _root_.Units.QuantityDimensions _root_.Units.EngineeringQuantities
  _root_.EngineeringScaling

/-! ## A. Exponents -/

-- `specificHeatCapacityDim = L² T⁻² Θ⁻¹`.
example :
    specificHeatCapacityDim.exponent .length = 2 ∧
      specificHeatCapacityDim.exponent .mass = 0 ∧
      specificHeatCapacityDim.exponent .time = -2 ∧
      specificHeatCapacityDim.exponent .current = 0 ∧
      specificHeatCapacityDim.exponent .temperature = -1 ∧
      specificHeatCapacityDim.exponent .amount = 0 ∧
      specificHeatCapacityDim.exponent .luminousIntensity = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact specificHeatCapacityDim_exponent _

-- `thermalConductivityDim = M L T⁻³ Θ⁻¹`.
example :
    thermalConductivityDim.exponent .length = 1 ∧
      thermalConductivityDim.exponent .mass = 1 ∧
      thermalConductivityDim.exponent .time = -3 ∧
      thermalConductivityDim.exponent .current = 0 ∧
      thermalConductivityDim.exponent .temperature = -1 ∧
      thermalConductivityDim.exponent .amount = 0 ∧
      thermalConductivityDim.exponent .luminousIntensity = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact thermalConductivityDim_exponent _

-- `heatTransferCoefficientDim = M T⁻³ Θ⁻¹` has no length exponent.
example :
    heatTransferCoefficientDim.exponent .length = 0 ∧
      heatTransferCoefficientDim.exponent .mass = 1 ∧
      heatTransferCoefficientDim.exponent .time = -3 ∧
      heatTransferCoefficientDim.exponent .temperature = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact heatTransferCoefficientDim_exponent _

-- Velocity, acceleration, density and viscosity at length and time.
example :
    velocityDim.exponent .length = 1 ∧ velocityDim.exponent .time = -1 ∧
      accelerationDim.exponent .time = -2 ∧ massDensityDim.exponent .length = -3 ∧
      dynamicViscosityDim.exponent .length = -1 ∧
      dynamicViscosityDim.exponent .time = -1 :=
  ⟨velocityDim_exponent _, velocityDim_exponent _, accelerationDim_exponent _,
    massDensityDim_exponent _, dynamicViscosityDim_exponent _, dynamicViscosityDim_exponent _⟩

/-! ## B. Dimension identities -/

-- The Reynolds, Prandtl, Nusselt (and Biot), Rayleigh and Froude
-- monomials are dimensionless.
example :
    massDensityDim * velocityDim * single .length / dynamicViscosityDim = 1 ∧
      dynamicViscosityDim * specificHeatCapacityDim / thermalConductivityDim = 1 ∧
      heatTransferCoefficientDim * single .length / thermalConductivityDim = 1 ∧
      accelerationDim * temperatureDim⁻¹ * temperatureDim * single .length ^ 3 /
        (diffusivityDim * diffusivityDim) = 1 ∧
      velocityDim / (accelerationDim * single .length) ^ (1 / 2 : Exponent) = 1 :=
  ⟨reynoldsNumber_dimensionless, prandtlNumber_dimensionless, nusseltNumber_dimensionless,
    rayleighNumber_dimensionless, froudeNumber_dimensionless⟩

/-! ## C. Coordinate formulas on concrete values -/

-- Water near room temperature: `μ = 1 / 1000`, `c_p = 4180`,
-- `k = 3 / 5` gives `Pr = 209 / 30`.
example : prandtlNumber ⟨1 / 1000⟩ ⟨4180⟩ ⟨3 / 5⟩ (by norm_num) = 209 / 30 := by
  rw [prandtlNumber_val]
  norm_num

-- The same `h = 10` and `L = 1 / 10`: `Nu = 40` against a fluid
-- conductivity `1 / 40`, and `Bi = 1 / 50` against a solid
-- conductivity `50`.
example :
    nusseltNumber ⟨10⟩ ⟨1 / 10⟩ ⟨1 / 40⟩ (by norm_num) = 40 ∧
      biotNumber ⟨10⟩ ⟨1 / 10⟩ ⟨50⟩ (by norm_num) = 1 / 50 := by
  rw [nusseltNumber_val, biotNumber_val]
  norm_num

-- `g = 10`, `β = 1 / 300`, `ΔT = 30`, `L = 1`, `ν = κ = 1 / 1000`
-- gives `Ra = 1000000`.
example :
    rayleighNumber ⟨10⟩ ⟨1 / 300⟩ ⟨30⟩ ⟨1⟩ ⟨1 / 1000⟩ ⟨1 / 1000⟩ (by norm_num) (by norm_num) =
      1000000 := by
  rw [rayleighNumber_val]
  norm_num

-- `U = 170`, `a = 340` gives `Ma = 1 / 2`.
example : machNumber ⟨170⟩ ⟨340⟩ (by norm_num) = 1 / 2 := by
  rw [machNumber_val]
  norm_num

-- `Re`, `Ma` and `Fr` use the speed `|U|` and `Ra` uses `|g|`:
-- reversing the velocity or the vertical axis (`g = -10`) leaves them
-- unchanged. `ΔT` keeps its sign: a negative `ΔT` gives a negative `Ra`.
example :
    reynoldsNumber ⟨1000⟩ ⟨-2⟩ ⟨1 / 10⟩ ⟨1 / 1000⟩ (by norm_num) = 200000 ∧
      machNumber ⟨-170⟩ ⟨340⟩ (by norm_num) = 1 / 2 ∧
      froudeNumber ⟨-3⟩ ⟨10⟩ ⟨5 / 2⟩ (by norm_num) = 3 / 5 ∧
      rayleighNumber ⟨-10⟩ ⟨1 / 300⟩ ⟨30⟩ ⟨1⟩ ⟨1 / 1000⟩ ⟨1 / 1000⟩ (by norm_num)
        (by norm_num) = 1000000 ∧
      rayleighNumber ⟨10⟩ ⟨1 / 300⟩ ⟨-30⟩ ⟨1⟩ ⟨1 / 1000⟩ ⟨1 / 1000⟩ (by norm_num)
        (by norm_num) = -1000000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [reynoldsNumber_val]
    norm_num
  · rw [machNumber_val]
    norm_num
  · unfold froudeNumber
    dsimp only
    rw [show (10 : ℝ) * (5 / 2) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  · rw [rayleighNumber_val]
    norm_num
  · rw [rayleighNumber_val]
    norm_num

/-! ## D. Unit invariance and the two-scale fixtures -/

-- The Prandtl number at arbitrary unit scales, read on coordinates.
example (u1 u2 : UnitScale ISQDimensionBase) (μ : WithDim dynamicViscosityDim ℝ)
    (cp : WithDim specificHeatCapacityDim ℝ) {k : WithDim thermalConductivityDim ℝ}
    (hk : 0 < k.val) :
    (u1.dimScale u2 dynamicViscosityDim : ℝ) * μ.val *
        ((u1.dimScale u2 specificHeatCapacityDim : ℝ) * cp.val) /
        ((u1.dimScale u2 thermalConductivityDim : ℝ) * k.val) =
      μ.val * cp.val / k.val := by
  have h := prandtlNumber_dimScale u1 u2 μ cp hk
  rwa [prandtlNumber_val, prandtlNumber_val] at h

-- `Re = 200000` and `Fr = 3 / 5` in base SI units and in the
-- millimetre scale.
example :
    reynoldsNumber ⟨1000⟩ ⟨2⟩ ⟨1 / 10⟩ ⟨1 / 1000⟩ (by norm_num) = 200000 ∧
      reynoldsNumber ⟨1 / 1000000⟩ ⟨2000⟩ ⟨100⟩ ⟨1 / 1000000⟩ (by norm_num) = 200000 ∧
      froudeNumber ⟨3⟩ ⟨10⟩ ⟨5 / 2⟩ (by norm_num) = 3 / 5 ∧
      froudeNumber ⟨3000⟩ ⟨10000⟩ ⟨2500⟩ (by norm_num) = 3 / 5 :=
  ⟨reynoldsNumber_si_mm.2.2.2.2.1, reynoldsNumber_si_mm.2.2.2.2.2,
    froudeNumber_si_mm.2.2.2.1, froudeNumber_si_mm.2.2.2.2⟩

/-! ## E. A molar heat capacity -/

-- A molar heat capacity is not mass-specific; divided by a molar
-- mass it is, and inserted unconverted it leaves a molar mass.
example :
    gasConstantDim ≠ specificHeatCapacityDim ∧
      gasConstantDim / molarMassDim = specificHeatCapacityDim ∧
      dynamicViscosityDim * gasConstantDim / thermalConductivityDim = molarMassDim :=
  ⟨gasConstantDim_ne_specificHeatCapacityDim, gasConstantDim_div_molarMassDim,
    dynamicViscosityDim_mul_gasConstantDim_div_thermalConductivityDim⟩

-- So the unconverted molar Prandtl expression is not unit invariant,
-- unlike `prandtlNumber_dimScale`.
example :
    ¬ ∀ (u1 u2 : UnitScale ISQDimensionBase) (μ c k : ℝ), 0 < μ → 0 < c → 0 < k →
      (u1.dimScale u2 dynamicViscosityDim : ℝ) * μ *
          ((u1.dimScale u2 gasConstantDim : ℝ) * c) /
          ((u1.dimScale u2 thermalConductivityDim : ℝ) * k) = μ * c / k := by
  intro h
  obtain ⟨u1, u2, μ, c, k, hμ, hc, hk, hne⟩ := molarPrandtl_not_unitInvariant
  exact hne (h u1 u2 μ c k hμ hc hk)

/-! ## F. A scaled transport field -/

-- The nonconstant field `ĉ(t̂, x̂) = t̂ + x̂²` with `L = 2`, `U = 3`, `C0 = 1`, at the physical
-- point `(t, x) = (1, 2)`, which corresponds to `(t̂, x̂) = (3 / 2, 1)`.

-- Nonzero physical derivatives of the fixture: `c_t = 3 / 2`, `c_x = 1`, `c_xx = 1 / 2`.
example :
    deriv (fun t => scaledField 2 3 1 (fun s y => s + y ^ 2) t 2) 1 = 3 / 2 ∧
      deriv (fun x => scaledField 2 3 1 (fun s y => s + y ^ 2) 1 x) 2 = 1 ∧
      iteratedDeriv 2 (fun x => scaledField 2 3 1 (fun s y => s + y ^ 2) 1 x) 2 = 1 / 2 := by
  have hfunT : (fun t => scaledField 2 3 1 (fun s y => s + y ^ 2) t 2)
      = (fun t => 3 * t / 2 + (2 / 2) ^ 2) := by
    funext t
    simp only [scaledField, one_mul]
  have hderivT : HasDerivAt (fun t : ℝ => 3 * t / 2 + (2 / 2) ^ 2) (3 * 1 / 2) 1 := by
    have h := ((((hasDerivAt_id (1 : ℝ)).const_mul (3 : ℝ)).div_const (2 : ℝ)).add_const
      (((2 : ℝ) / 2) ^ 2))
    simpa using h
  have hT : deriv (fun t => scaledField 2 3 1 (fun s y => s + y ^ 2) t 2) 1 = 3 / 2 := by
    rw [hfunT, hderivT.deriv]
    norm_num
  have hfunX : (fun x => scaledField 2 3 1 (fun s y => s + y ^ 2) 1 x)
      = (fun x => 3 * 1 / 2 + (x / 2) * (x / 2)) := by
    funext x
    simp only [scaledField, pow_two, one_mul]
  have hder1 : ∀ x', deriv (fun x => scaledField 2 3 1 (fun s y => s + y ^ 2) 1 x) x'
      = x' / 2 := by
    intro x'
    have hinner : HasDerivAt (fun x => x / 2) (1 / 2) x' := by
      have h := (hasDerivAt_id x').div_const 2
      simpa using h
    have hmul : HasDerivAt (fun x => (x / 2) * (x / 2))
        ((1 / 2) * (x' / 2) + (x' / 2) * (1 / 2)) x' :=
      hinner.mul hinner
    have h : HasDerivAt (fun x => 3 * 1 / 2 + (x / 2) * (x / 2))
        ((1 / 2) * (x' / 2) + (x' / 2) * (1 / 2)) x' :=
      hmul.const_add (3 * 1 / 2)
    rw [hfunX, h.deriv]
    ring
  have hX : deriv (fun x => scaledField 2 3 1 (fun s y => s + y ^ 2) 1 x) 2 = 1 := by
    rw [hder1]
    norm_num
  have hfun2 : deriv (fun x => scaledField 2 3 1 (fun s y => s + y ^ 2) 1 x)
      = (fun x' => x' / 2) := funext hder1
  have h2 : HasDerivAt (fun x' : ℝ => x' / 2) (1 / 2) 2 := by
    have h := (hasDerivAt_id (2 : ℝ)).div_const (2 : ℝ)
    simpa using h
  have hXX : deriv (deriv (fun x => scaledField 2 3 1 (fun s y => s + y ^ 2) 1 x)) 2
      = 1 / 2 := by
    rw [hfun2]
    exact h2.deriv
  have e : iteratedDeriv 2 (fun x => scaledField 2 3 1 (fun s y => s + y ^ 2) 1 x)
      = deriv (deriv (fun x => scaledField 2 3 1 (fun s y => s + y ^ 2) 1 x)) := by
    have e1 := iteratedDeriv_succ
      (n := 1) (f := (fun x => scaledField 2 3 1 (fun s y => s + y ^ 2) 1 x))
    rwa [iteratedDeriv_one] at e1
  have hI : iteratedDeriv 2 (fun x => scaledField 2 3 1 (fun s y => s + y ^ 2) 1 x) 2
      = 1 / 2 := by
    rw [e]
    exact hXX
  exact ⟨hT, hX, hI⟩

-- `L = 2` makes an exponent error visible: the fixture's scaled second derivative is `2`, and
-- the first-power factor `C0 / L` would give `1`, not the actual `c_xx = 1 / 2`.
example :
    iteratedDeriv 2 (fun y => (fun s y : ℝ => s + y ^ 2) (3 * 1 / 2) y) (2 / 2) = 2 ∧
      iteratedDeriv 2 (fun x => scaledField 2 3 1 (fun s y => s + y ^ 2) 1 x) 2
        ≠ 1 / 2 * iteratedDeriv 2 (fun y => (fun s y : ℝ => s + y ^ 2) (3 * 1 / 2) y) (2 / 2) := by
  have hfun0 : (fun y => (fun s y : ℝ => s + y ^ 2) (3 * 1 / 2) y)
      = (fun y : ℝ => 3 * 1 / 2 + y * y) := by
    funext y
    simp only [pow_two]
  have hder1 : ∀ y', deriv (fun y : ℝ => 3 * 1 / 2 + y * y) y' = 1 * y' + y' * 1 := by
    intro y'
    have hid : HasDerivAt (fun y : ℝ => y) 1 y' := hasDerivAt_id' y'
    have hmul : HasDerivAt (fun y : ℝ => y * y) (1 * y' + y' * 1) y' := hid.mul hid
    have h : HasDerivAt (fun y : ℝ => 3 * 1 / 2 + y * y) (1 * y' + y' * 1) y' :=
      hmul.const_add (3 * 1 / 2)
    exact h.deriv
  have hfun2 : deriv (fun y : ℝ => 3 * 1 / 2 + y * y) = (fun y' : ℝ => 2 * y') := by
    funext y'
    show deriv (fun y : ℝ => 3 * 1 / 2 + y * y) y' = 2 * y'
    rw [hder1]
    ring
  have h2 : HasDerivAt (fun y' : ℝ => 2 * y') (2 * 1) (2 / 2) := by
    have h := (hasDerivAt_id ((2 : ℝ) / 2)).const_mul (2 : ℝ)
    simpa using h
  have h1 : iteratedDeriv 2 (fun y => (fun s y : ℝ => s + y ^ 2) (3 * 1 / 2) y) (2 / 2)
      = 2 := by
    have e : iteratedDeriv 2 (fun y : ℝ => 3 * 1 / 2 + y * y)
        = deriv (deriv (fun y : ℝ => 3 * 1 / 2 + y * y)) := by
      have e1 := iteratedDeriv_succ
        (n := 1) (f := (fun y : ℝ => 3 * 1 / 2 + y * y))
      rwa [iteratedDeriv_one] at e1
    rw [hfun0, e, hfun2, h2.deriv]
    norm_num
  have hc : ContDiff ℝ 2 (Function.uncurry fun s y : ℝ => s + y ^ 2) := by
    change ContDiff ℝ 2 (fun p : ℝ × ℝ => p.1 + p.2 ^ 2)
    fun_prop
  have h2v : iteratedDeriv 2 (fun x => scaledField 2 3 1 (fun s y => s + y ^ 2) 1 x) 2
      = 1 / 2 := by
    rw [iteratedDeriv_two_scaledField_space hc 2 3 1 1 2, h1]
    norm_num
  refine ⟨h1, ?_⟩
  rw [h2v, h1]
  norm_num

end PhyslibExtTest.ContinuumMechanics.EngineeringScaling
