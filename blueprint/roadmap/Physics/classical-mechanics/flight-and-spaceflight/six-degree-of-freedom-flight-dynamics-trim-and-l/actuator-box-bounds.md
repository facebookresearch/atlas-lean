# Speed and actuator bounds on the actuator box

For every state `(x, z, θ, q)` of the [actuator box](actuator-box.md):

- the [flight speed](flight-speed.md) satisfies `V ≥ 99/100`;
- the forward component `A₁` of the [actuator force](actuator-force.md) satisfies
  `1/10 < A₁ < 1/5`, and its upward component satisfies `|A₂| < 1/20`;
- the [pitch-moment actuator](pitch-moment.md) satisfies `|M| ≤ 3/100`.
