/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Units.ElectricalDimensions
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Units.ElectricalDimensions

namespace PhyslibExtTest.Units.ElectricalDimensions

/-- The named identities, exercised one by one. -/
example : dimMul currentDim timeDim = chargeDim := current_mul_time
example : dimMul voltageDim currentDim = powerDim := voltage_mul_current
example : dimMul resistanceDim capacitanceDim = timeDim :=
  resistance_mul_capacitance
example : dimDiv inductanceDim resistanceDim = timeDim :=
  inductance_div_resistance
example : dimMul conductanceDim resistanceDim = dimensionlessDim :=
  conductance_mul_resistance

/-- The bundled headline identities, through the public lemma. -/
example : dimMul voltageDim currentDim = powerDim ∧
    dimMul resistanceDim capacitanceDim = timeDim ∧
    dimDiv inductanceDim resistanceDim = timeDim ∧
    dimMul currentDim timeDim = chargeDim :=
  electrical_dimensions_product_identities

end PhyslibExtTest.Units.ElectricalDimensions
