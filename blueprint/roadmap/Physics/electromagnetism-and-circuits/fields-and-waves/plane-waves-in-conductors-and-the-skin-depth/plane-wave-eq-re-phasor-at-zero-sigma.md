# Plane Wave eq re phasor at zero sigma

At zero conductivity, the real cosine plane wave with wavenumber
the phase constant `beta` is the real part of
`exp (i * (beta * x - omega * t)) * E0`. This is the complex conjugate
of the forward phasor `exp (i * (omega * t - beta * x)) * E0` of the
declared convention, that is the phasor of the opposite time
convention; the two have the same real part because cosine is even,
so this identity does not check the sign convention. The phasor of
the declared convention is
`planeWave_eq_re_forward_phasor_at_zero_sigma`.
