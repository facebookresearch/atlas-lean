# Potential temp buoyancy accel

Buoyancy acceleration of a dry parcel displaced by `zeta` in a locally
linear potential-temperature profile `theta(z) = theta0 + a * z`: the
parcel keeps `theta0`, the ambient value at `zeta` is `theta0 + a * zeta`,
so the acceleration is `-(g * a / theta0) * zeta` (Holton and Hakim,
§2.7.3, under the approximations listed in the module docstring).
