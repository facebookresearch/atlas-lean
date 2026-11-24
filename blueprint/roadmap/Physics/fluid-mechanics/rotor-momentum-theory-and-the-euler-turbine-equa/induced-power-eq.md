# Under the port laws, the induced power is minus the extracted power

Let an [actuator-disk state](actuator-disk.md) satisfy the [port laws](port-laws.md): Bernoulli
`p∞ + ρ U∞² / 2 = p⁺ + ρ U_d² / 2` upstream and `p⁻ + ρ U_d² / 2 = p∞ + ρ U_w² / 2` downstream of
the disk, and the momentum balances `F = A (p⁺ - p⁻)` of the thin disk and `F = ρ A U_d (U∞ - U_w)`
of the streamtube, where `F` is the axial force of the fluid on the disk, positive along the flow,
and let `T` be a real number with `F = -T`. Then the [induced power](induced-power.md) is the
negative of the [extracted power](extracted-power.md) `F U_d`: it is the power `-F U_d` of the disk
on the stream, and it equals `T U_d`, with `T = -F` the rotor thrust. No still-air, sign or powered
assumption is made, so the identities also cover reversed and zero-thrust states, which the
[hover power](hover-power-eq.md) formula excludes. In the physical reading `ρ > 0` and `A > 0`; the
identities need no sign condition.
