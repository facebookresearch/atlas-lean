/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Basic

/-!
# Electrical dimensions

## i. Overview

Dimension vectors for electrical quantities in a four-coordinate
(length, mass, time, charge) exponent lattice with componentwise
addition as the group law, as declared by the roadmap leaf. The
named electrical dimensions (current, voltage, resistance,
capacitance, inductance, conductance, permittivity, permeability,
power) are defined from the base dimensions, and the module proves
the product/division identities among them, for example
`current * time = charge` and `voltage * current = power`. These
are dimension identities only: no unit conversion factor and no
physical quantity is introduced.

## ii. Key results

- `electrical_dimensions_product_identities`: the bundled
  identities among the named electrical dimensions.
- The individual identities (`current_mul_time`,
  `voltage_mul_current`, `resistance_mul_capacitance`,
  `inductance_div_resistance`, `conductance_mul_resistance`,
  `permittivity_mul_length`, `permeability_mul_length`).

## iii. Table of contents

- A. Electrical dimension vectors

## iv. References

- Bureau International des Poids et Mesures, *The International
  System of Units (SI Brochure)*, ninth edition, 2019: the base
  and derived electrical quantities whose dimension exponents are
  tabulated here.

## A. Electrical dimension vectors

Discharges ECE roadmap leaf `ECE.INT.UNITS.L1` (electrical
dimension identities).
-/

@[expose] public section

namespace PhyslibExt.Units.ElectricalDimensions

/-- Exponent vector of a dimension over the charge-based bases
`(L, M, T, C)`. Pin-stage stand-in for the canonical Physlib `Dimension`;
see the module header for the implementation-time replacement. -/
abbrev DimVec := ℤ × ℤ × ℤ × ℤ

/-- Dimension multiplication: componentwise addition of exponents. -/
def dimMul (d e : DimVec) : DimVec :=
  (d.1 + e.1, d.2.1 + e.2.1, d.2.2.1 + e.2.2.1, d.2.2.2 + e.2.2.2)

/-- Inverse dimension: negation of exponents. -/
def dimInv (d : DimVec) : DimVec :=
  (-d.1, -d.2.1, -d.2.2.1, -d.2.2.2)

/-- Dimension division: `d / e = d * e⁻¹` on exponents. -/
def dimDiv (d e : DimVec) : DimVec :=
  dimMul d (dimInv e)

/-- Dimension power: scalar multiplication of exponents. -/
def dimPow (d : DimVec) (n : ℤ) : DimVec :=
  (n * d.1, n * d.2.1, n * d.2.2.1, n * d.2.2.2)

/-- Length dimension `L = (1,0,0,0)`. -/
def lengthDim : DimVec := (1, 0, 0, 0)

/-- Mass dimension `M = (0,1,0,0)`. -/
def massDim : DimVec := (0, 1, 0, 0)

/-- Time dimension `T = (0,0,1,0)`. -/
def timeDim : DimVec := (0, 0, 1, 0)

/-- Charge dimension `C = (0,0,0,1)`. -/
def chargeDim : DimVec := (0, 0, 0, 1)

/-- Dimensionless dimension `1 = (0,0,0,0)`. -/
def dimensionlessDim : DimVec := (0, 0, 0, 0)

/-- Power dimension `M*L^2/T^3 = (2,1,-3,0)`. -/
def powerDim : DimVec := (2, 1, -3, 0)

/-- Current dimension `C/T`. -/
def currentDim : DimVec :=
  dimDiv chargeDim timeDim

/-- Voltage dimension `M*L^2/(T^2*C)`. -/
def voltageDim : DimVec :=
  dimDiv (dimMul massDim (dimPow lengthDim 2))
    (dimMul (dimPow timeDim 2) chargeDim)

/-- Resistance dimension `M*L^2/(T*C^2)`. -/
def resistanceDim : DimVec :=
  dimDiv (dimMul massDim (dimPow lengthDim 2))
    (dimMul timeDim (dimPow chargeDim 2))

/-- Capacitance dimension `C^2*T^2/(M*L^2)`. -/
def capacitanceDim : DimVec :=
  dimDiv (dimMul (dimPow chargeDim 2) (dimPow timeDim 2))
    (dimMul massDim (dimPow lengthDim 2))

/-- Inductance dimension `M*L^2/C^2`. -/
def inductanceDim : DimVec :=
  dimDiv (dimMul massDim (dimPow lengthDim 2)) (dimPow chargeDim 2)

/-- Conductance dimension: inverse resistance. -/
def conductanceDim : DimVec :=
  dimInv resistanceDim

/-- Permittivity dimension: capacitance per length, `capacitance/L`. -/
def permittivityDim : DimVec :=
  dimDiv capacitanceDim lengthDim

/-- Permeability dimension: inductance per length, `inductance/L`. -/
def permeabilityDim : DimVec :=
  dimDiv inductanceDim lengthDim

/-- Charge conversion: current times time has charge dimension, `I * T = C`.
This is the exponent-level content of the `toISQHom` charge = SI current ×
time conversion (see module header). -/
lemma current_mul_time :
    dimMul currentDim timeDim = chargeDim := by
  decide

/-- Voltage times current has power dimension: `V * I = P`. -/
lemma voltage_mul_current :
    dimMul voltageDim currentDim = powerDim := by
  decide

/-- Resistance times capacitance has time dimension: `R * C = T`. -/
lemma resistance_mul_capacitance :
    dimMul resistanceDim capacitanceDim = timeDim := by
  decide

/-- Inductance over resistance has time dimension: `L_ind / R = T`. -/
lemma inductance_div_resistance :
    dimDiv inductanceDim resistanceDim = timeDim := by
  decide

/-- Conductance is inverse resistance: `G * R = 1` (dimensionless). -/
lemma conductance_mul_resistance :
    dimMul conductanceDim resistanceDim = dimensionlessDim := by
  decide

/-- Permittivity times length is capacitance: `ε * L = C_cap`. -/
lemma permittivity_mul_length :
    dimMul permittivityDim lengthDim = capacitanceDim := by
  decide

/-- Permeability times length is inductance: `μ * L = L_ind`. -/
lemma permeability_mul_length :
    dimMul permeabilityDim lengthDim = inductanceDim := by
  decide

/-- Headline: the electrical dimension product identities. Voltage times
current has power dimension; resistance times capacitance and inductance
over resistance each have time dimension; current times time has charge
dimension (the `toISQHom` charge conversion). -/
lemma electrical_dimensions_product_identities :
    dimMul voltageDim currentDim = powerDim ∧
      dimMul resistanceDim capacitanceDim = timeDim ∧
      dimDiv inductanceDim resistanceDim = timeDim ∧
      dimMul currentDim timeDim = chargeDim := by
  decide

end PhyslibExt.Units.ElectricalDimensions
