# Rotor Current

Rotor current in the Thevenin equivalent: the Thevenin voltage divided
by the impedance with real part `Rth + R2 / s` and reactance `Xeq`. It is
written with the slip division cleared, as `Vth s / (Rth s + R2 + i Xeq s)`,
so that no reciprocal of the slip appears: at nonzero slip it equals the
quotient (`rotorCurrent_eq_div`), and at zero slip it is zero
(`rotorCurrent_zero_slip`), the physical value at synchronous speed.
