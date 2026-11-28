# Engineering ISQ dimensions and unit conversions

## Engineering dimension names and exponents

- [Dimension of force](force-dim.md)
- [Dimension of power in the ISQ](power-dim.md)
- [Dimension of mass flow rate](mass-flow-dim.md)
- [Dimension of molar flow rate](molar-flow-dim.md)
- [Dimension of impulse](impulse-dim.md)
- [Dimension of translational stiffness](translational-stiffness-dim.md)
- [Dimension of torsional stiffness](torsional-stiffness-dim.md)
- [Dimension of the Faraday constant](faraday-dim.md)
- [Exponents of the force dimension](force-dim-exponent.md)
- [Exponents of the power dimension](power-dim-exponent.md)
- [Exponents of the mass flow rate dimension](mass-flow-dim-exponent.md)
- [Exponents of the molar flow rate dimension](molar-flow-dim-exponent.md)
- [Exponents of the impulse dimension](impulse-dim-exponent.md)
- [Exponents of the translational stiffness dimension](translational-stiffness-dim-exponent.md)
- [Exponents of the torsional stiffness dimension](torsional-stiffness-dim-exponent.md)
- [Exponents of the Faraday constant dimension](faraday-dim-exponent.md)

## Dimension identities and invalid identifications

- [Force times length has the dimension of energy](force-dim-mul-length.md)
- [Stress times area is force](stress-dim-mul-area.md)
- [Power times time is energy in the ISQ](power-dim-mul-time.md)
- [Molar mass times molar flow rate is mass flow rate](molar-mass-dim-mul-molar-flow-dim.md)
- [Faraday constant times amount is charge](faraday-dim-mul-amount-dim.md)
- [A newton metre is not a newton per metre](force-dim-mul-length-ne-div-length.md)
- [Mass flow rate differs from molar flow rate](mass-flow-dim-ne-molar-flow-dim.md)
- [Molar flow rate is not a particle rate](molar-flow-dim-ne-inv-time.md)

## Rescaling of engineering quantities

- [Stress times area rescales as a force](stress-mul-area-with-dim-dim-scale.md)
- [Stress factor times area factor is the force factor](dim-scale-stress-mul-area.md)
- [Power factor times time factor is the energy factor](dim-scale-power-mul-time.md)
- [Molar mass factor times molar flow factor is the mass flow factor](dim-scale-molar-mass-mul-molar-flow.md)
- [Torsional stiffness and energy rescale alike](dim-scale-torsional-stiffness-eq-energy.md)

## Concrete conversions

- [Unit scale with unit magnitudes](si-scale.md)
- [Millimetre unit scale](mm-scale.md)
- [Force factor from metres to millimetres](dim-scale-si-mm-force-dim.md)
- [Stress factor from metres to millimetres](dim-scale-si-mm-stress-dim.md)
- [Force of 5 from metres to millimetres and back](force-fixture-round-trip.md)
- [Stress of 2 from metres to millimetres and back](stress-fixture-round-trip.md)
- [Force conversion round trip](force-dim-dim-scale-round-trip.md)
- [Stress conversion round trip](stress-dim-dim-scale-round-trip.md)
- [Typed force conversion round trip](force-with-dim-round-trip.md)

## Dimension identities of the three formulas

- [Torque times angular velocity has the dimension of power](torque-mul-angular-velocity.md)
- [Density times velocity times area is mass flow rate](density-mul-velocity-mul-area.md)

## Rescaling of the three formulas

- [Power factor is the torque factor times the angular velocity factor](dim-scale-torque-mul-angular-velocity.md)
- [Mass flow factor is the product of density, velocity and area factors](dim-scale-density-mul-velocity-mul-area.md)

## The real-coordinate formulas commute with a change of units

- [Normal stress formula commutes with unit changes](normal-stress-coord-dim-scale.md)
- [Shaft power formula commutes with unit changes](shaft-power-coord-dim-scale.md)
- [Mass flow rate formula commutes with unit changes](mass-flow-rate-coord-dim-scale.md)

## Restoring the output quantity

- [Normal stress](normal-stress.md)
- [Shaft power](shaft-power.md)
- [Mass flow rate](mass-flow-rate.md)
- [Coordinate of the normal stress](normal-stress-val.md)
- [Coordinate of the shaft power](shaft-power-val.md)
- [Coordinate of the mass flow rate](mass-flow-rate-val.md)
- [Normal stress computed in new units and converted back](normal-stress-coord-round-trip.md)
- [Shaft power computed in new units and converted back](shaft-power-coord-round-trip.md)
- [Typed normal stress commutes with unit changes](normal-stress-dim-scale.md)
- [Typed shaft power commutes with unit changes](shaft-power-dim-scale.md)
- [Typed mass flow rate commutes with unit changes](mass-flow-rate-dim-scale.md)
- [Mass flow rate conversion round trip](mass-flow-rate-coord-round-trip.md)

## Nonzero conversions

- [Normal stress from metres to millimetres](normal-stress-si-mm.md)
- [Shaft power from metres to millimetres](shaft-power-si-mm.md)
- [Mass flow rate from metres to millimetres](mass-flow-rate-si-mm.md)

## Invalid and boundary examples

- [Force and area have different dimensions](force-dim-ne-area.md)
- [Sum of a force and an area has no conversion factor](force-add-area-not-dim-scale.md)
- [Force over area does not convert as a force](normal-stress-coord-ne-force-dim.md)
- [Twice the normal stress formula also commutes with a change of units](two-mul-normal-stress-coord-dim-scale.md)
