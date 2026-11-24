# Dimensions of engineering quantities

## Engineering dimensions and their exponents

- [Dimension of force](force-dim.md)
- [Dimension of power](power-dim.md)
- [Dimension of mass flow rate](mass-flow-dim.md)
- [Dimension of molar flow rate](molar-flow-dim.md)
- [Dimension of impulse](impulse-dim.md)
- [Dimension of translational stiffness](translational-stiffness-dim.md)
- [Dimension of torsional stiffness per radian](torsional-stiffness-dim.md)
- [Dimension of the Faraday constant](faraday-dim.md)
- [Exponents of the force dimension](force-dim-exponent.md)
- [Exponents of the power dimension](power-dim-exponent.md)
- [Exponents of the mass-flow-rate dimension](mass-flow-dim-exponent.md)
- [Exponents of the molar-flow-rate dimension](molar-flow-dim-exponent.md)
- [Exponents of the impulse dimension](impulse-dim-exponent.md)
- [Exponents of the translational-stiffness dimension](translational-stiffness-dim-exponent.md)
- [Exponents of the torsional-stiffness dimension](torsional-stiffness-dim-exponent.md)
- [Exponents of the Faraday-constant dimension](faraday-dim-exponent.md)

## Dimension identities and invalid identifications

- [Force times length and torsional stiffness have the energy dimension](force-dim-mul-length.md)
- [Stress is force per area](stress-dim-mul-area.md)
- [Power times time is energy](power-dim-mul-time.md)
- [Molar mass times molar flow rate is a mass flow rate](molar-mass-dim-mul-molar-flow-dim.md)
- [The Faraday constant times an amount is an electric charge](faraday-dim-mul-amount-dim.md)
- [A newton metre is not a newton per metre](force-dim-mul-length-ne-div-length.md)
- [A mass flow rate is not a molar flow rate](mass-flow-dim-ne-molar-flow-dim.md)
- [A molar flow rate is not a particle rate](molar-flow-dim-ne-inv-time.md)

## Conversion factors of force, stress, power and flows

- [Converting a force to other units and back returns it](force-dim-dim-scale-round-trip.md)
- [Converting a stress value to other units and back returns it](stress-dim-dim-scale-round-trip.md)
- [Stress times area converts with the force factor](stress-mul-area-with-dim-dim-scale.md)
- [Stress factor times area factor is the force factor](dim-scale-stress-mul-area.md)
- [Power factor times time factor is the energy factor](dim-scale-power-mul-time.md)
- [Molar-mass factor times molar-flow factor is the mass-flow factor](dim-scale-molar-mass-mul-molar-flow.md)
- [Torsional stiffness and energy have the same conversion factor](dim-scale-torsional-stiffness-eq-energy.md)

## Metre-to-millimetre examples

- [Units with magnitude one at every base quantity](si-scale.md)
- [Units with the millimetre as length unit](mm-scale.md)
- [From metres to millimetres, force values are multiplied by 1000](dim-scale-si-mm-force-dim.md)
- [From metres to millimetres, stress values are divided by 1000](dim-scale-si-mm-stress-dim.md)
- [A force of 5 base units is 5000 in millimetre units and back](force-fixture-round-trip.md)
- [A stress of 2 base units is 1 / 500 in millimetre units and back](stress-fixture-round-trip.md)

## Dimensions of the stress, shaft-power and mass-flow formulas

- [Torque times angular velocity is power](torque-mul-angular-velocity.md)
- [Density times velocity times area is a mass flow rate](density-mul-velocity-mul-area.md)

## Conversion factors of the three formulas

- [The stress factor is the force factor over the area factor](dim-scale-force-dim-mul-inv-area.md)
- [Torque factor times angular-velocity factor is the power factor](dim-scale-torque-mul-angular-velocity.md)
- [Density, velocity and area factors multiply to the mass-flow factor](dim-scale-density-mul-velocity-mul-area.md)

## The three formulas commute with a change of units

- [Normal stress F / A commutes with every change of units](normal-stress-coord-dim-scale.md)
- [Shaft power τ ω commutes with every change of units](shaft-power-coord-dim-scale.md)
- [Mass flow rate ρ v A commutes with every change of units](mass-flow-rate-coord-dim-scale.md)

## Typed outputs, their conversion and round trips

- [Normal stress F / A as a typed quantity](normal-stress.md)
- [Shaft power τ ω as a typed quantity](shaft-power.md)
- [Mass flow rate ρ v A as a typed quantity](mass-flow-rate.md)
- [The typed normal stress has value F / A](normal-stress-val.md)
- [The typed shaft power has value τ ω](shaft-power-val.md)
- [The typed mass flow rate has value ρ v A](mass-flow-rate-val.md)
- [Stress computed in new units and converted back is unchanged](normal-stress-coord-round-trip.md)
- [Shaft power computed in new units and converted back is unchanged](shaft-power-coord-round-trip.md)
- [Mass flow rate computed in new units and converted back is unchanged](mass-flow-rate-coord-round-trip.md)

## Metre-to-millimetre examples for the three formulas

- [From metres to millimetres, the stress 5 / 2 becomes 1 / 400](normal-stress-si-mm.md)
- [From metres to millimetres, the shaft power 12 becomes 12000000](shaft-power-si-mm.md)
- [From metres to millimetres, the mass flow rate 20 stays 20](mass-flow-rate-si-mm.md)

## Invalid and boundary examples

- [Force and area have different dimensions](force-dim-ne-area.md)
- [A sum of a force and an area converts like no dimension](force-add-area-not-dim-scale.md)
- [Read as a force, F / A does not convert correctly](normal-stress-coord-ne-force-dim.md)
- [The wrong stress 2 F / A also commutes with changes of units](two-mul-normal-stress-coord-dim-scale.md)
