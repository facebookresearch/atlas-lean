# To Lp sensor eq to Euclidean Lin add offset

Sensor reading in Gaussian-interface coordinates: at
positive-definite fixed supported stiffness, a supported displacement
`u` solving the supported system at load `f0 + Bload *ᵥ ofLp θ` is
read by the sensors, as a Euclidean vector, as the observation matrix
applied to `θ` plus the deterministic offset of the known load `f0`.
Uses the supported inverse characterization
`supported_mulVec_eq_iff_inv_mulVec`.
