# Premises of a circular orbit of radius R in the orbit plane

For reals `μ` and `R` and functions `r, v : ℝ → ℂ` of time, a planar position and velocity relative
to the attracting center (complex numbers: the real part is the coordinate along the first in-plane
axis, the imaginary part the coordinate along the second), the circular-orbit premises are:

- the gravitational parameter is positive, `μ > 0`;
- the radius is positive, `R > 0`, which excludes the collision orbit `R = 0`;
- the position stays on the circle of radius `R` about the center: `|r(t)| = R` for every real
  time `t`, with `|·|` the modulus of a complex number;
- the velocity is the time derivative of the position: `r'(t) = v(t)` for every `t`;
- the acceleration is the inverse-square attraction toward the center:
  `v'(t) = −(μ / |r(t)|³) r(t)` for every `t`.
