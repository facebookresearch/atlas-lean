# Rotor momentum theory and the Euler turbine equation

## Lumped ports about the shaft

- [Shaft axis e₃ = (0, 0, 1)](shaft-axis.md)
- [Local cylindrical frame at azimuth φ, the rotation by φ about e₃](cyl-frame.md)
- [Lumped meanline port of a rotor control volume](rotor-port.md)
- [Representative point o + r e_r + z e₃ of a port](point.md)
- [Inertial velocity c_r e_r + c_θ e_θ + c_z e₃ at a port](velocity.md)
- [Outward unit normal n_r e_r + n_z e₃ at a port](normal.md)
- [Lumped mass flow ρ A (c · n) of a port](lumped-mass-flow.md)
- [Area-weighted local momentum flux ṁ c + p A n of a port](local-momentum-flux.md)
- [Lumped axial angular-momentum flux of a port about the shaft](axial-moment-flux.md)
- [The local momentum flux is A times the momentum flux with stress −p 1](local-momentum-flux-eq-momentum-flux.md)
- [Lumped mass flow ρ A (c_r n_r + c_z n_z) in cylindrical components](lumped-mass-flow-eq.md)
- [The lumped axial angular-momentum flux of a port is ṁ r c_θ](axial-moment-flux-eq.md)

## The Euler torque on the fluid

- [Euler torque τ = ṁ (r₂ c_θ₂ − r₁ c_θ₁) − M_ext from the balances](torque-on-fluid-eq.md)

## Power on the fluid and shaft power out

- [Axial torque e₃ · Σ (x_k − o) × F_k of finitely many forces](axial-torque.md)
- [Power of forces at points of a rotor turning at ω about e₃](rotor-power.md)
- [The power of forces at points of a rotor is ω times their axial torque](rotor-power-eq.md)
- [With no other external moment, P = ω τ = ṁ (U₂ c_θ₂ − U₁ c_θ₁)](power-on-fluid-eq.md)
- [Shaft power out of a steady rotor is minus the power on the fluid](shaft-power-out-eq.md)
- [Equal r c_θ at both ports gives zero torque, power and shaft power](torque-on-fluid-eq-zero-of-specific-angu.md)
- [Compressor sign: for ṁ > 0, P > 0 exactly when U₁ c_θ₁ < U₂ c_θ₂](compressor-iff.md)
- [Turbine sign: for ṁ > 0, W_out > 0 exactly when U₂ c_θ₂ < U₁ c_θ₁](turbine-iff.md)
- [The swirl relative to a rotor turning at ω is c_θ − ω r](relative-swirl-eq.md)

## The actuator disk and its port laws

- [State of an ideal actuator disk in a steady stream](actuator-disk.md)
- [Port laws of the ideal actuator disk](port-laws.md)
- [Freestream kinetic power ρ A U³ / 2 through the area A](power-normalization.md)

## Disk speed and pressure jump

- [Pressure jump p⁺ − p⁻ = ρ (U∞² − U_w²) / 2 from the port laws](pressure-jump-eq.md)
- [For ρ, A > 0 and U_w ≠ U∞, the disk speed is U_d = (U∞ + U_w) / 2](u-disk-eq.md)
- [Extracted power T U_d of an actuator disk](extracted-power.md)
- [Extracted power T U_d = ṁ (U∞² − U_w²) / 2 under the port laws](extracted-power-eq.md)
- [For 0 ≤ U_w < U∞ and ρ > 0, the total pressure drops across the disk](total-pressure-drop.md)

## Power coefficient and the Betz limit

- [Axial induction factor a = 1 − U_d / U∞](induction-factor.md)
- [Power coefficient C_P = T U_d / (ρ A U∞³ / 2)](power-coefficient.md)
- [For ρ, A, U∞ > 0 and U_w ≠ U∞, C_P = 4 a (1 − a)²](power-coefficient-eq.md)
- [For 0 ≤ a < 1/2, 4 a (1 − a)² ≤ 16/27 with equality exactly at a = 1/3](betz-bound.md)
- [Betz limit C_P ≤ 16/27 for 0 < U_w < U∞ and ρ, A > 0](power-coefficient-le-betz.md)
- [Actuator-disk state with induction factor a](of-induction.md)
- [Every induction factor is realized by a state satisfying the port laws](of-induction-spec.md)

## The hovering rotor

- [Induced power ṁ (U_w² − U∞²) / 2 of an actuator disk](induced-power.md)
- [Under the port laws, the induced power is minus the extracted power](induced-power-eq.md)
- [In still air with a nonzero force, the far wake moves at U_w = 2 v_i](hover-u-wake-eq.md)
- [Hover thrust T = 2 ρ A v_i² for a positive thrust in still air](hover-thrust-eq.md)
- [Powered hover: induced velocity v_i = √(T / (2 ρ A))](hover-induced-velocity-eq.md)
- [Powered hover: induced power P = T v_i = T √(T / (2 ρ A))](hover-power-eq.md)
