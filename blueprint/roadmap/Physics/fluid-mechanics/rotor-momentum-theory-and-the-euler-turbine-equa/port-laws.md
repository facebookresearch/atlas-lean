# Port laws of the ideal actuator disk

An [actuator-disk state](actuator-disk.md) satisfies the port laws, the model inputs of
one-dimensional momentum theory, when, with `T` the axial force of the fluid on the disk (positive
along the flow):

- Bernoulli holds from far upstream to the upstream face of the disk:
  `p∞ + ρ U∞² / 2 = p⁺ + ρ U_d² / 2`;
- Bernoulli holds from the downstream face of the disk to the far wake:
  `p⁻ + ρ U_d² / 2 = p∞ + ρ U_w² / 2`;
- the momentum balance of the thin disk holds, the force is the pressure jump times the area:
  `T = A (p⁺ - p⁻)`;
- the momentum balance of the streamtube holds, the force is the mass flow `ρ A U_d` times the loss
  of axial speed: `T = ρ A U_d (U∞ - U_w)`.

Bernoulli is not applied across the disk, where the pressure jumps.
