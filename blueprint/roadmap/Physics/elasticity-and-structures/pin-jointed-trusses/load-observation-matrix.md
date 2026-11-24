# Load Observation Matrix

Load-parameter observation matrix at fixed supported stiffness:
`Cmat * K⁻¹ * Bload`, where `K` is the supported stiffness
`(axialCompatibility r a b * S)ᵀ * Matrix.diagonal k *
(axialCompatibility r a b * S)`. The truss data and weights `k` are
fixed knowns; only the load parameters multiplied by `Bload` are
unknown, so the parameter-to-observation map is linear. At a
non-invertible `K` the inverse is the totalized matrix inverse and the
physical reading needs positive definiteness, as in the theorems
below.
