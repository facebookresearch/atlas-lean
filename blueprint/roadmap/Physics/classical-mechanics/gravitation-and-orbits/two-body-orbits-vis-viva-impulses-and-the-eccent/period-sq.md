# Kepler's third law for a circular orbit: T² = 4 π² R³ / μ

For planar position and velocity functions `r, v : ℝ → ℂ` satisfying the
[circular-orbit premises](is-circular-orbit.md) with gravitational parameter `μ` and radius `R`
(`μ > 0`, `R > 0`, and for every real time `t`: `|r(t)| = R`, `r'(t) = v(t)` and
`v'(t) = −(μ / |r(t)|³) r(t)`), and every real time `t`, the period `T = 2 π R / |v(t)|`, the time
to travel the circumference `2 π R` at the speed `|v(t)|`, satisfies `T² = 4 π² R³ / μ`. This is
[Kepler's third law](../kepler-s-third-law-for-circular-orbits/kepler-third-law.md) with `G M = μ`;
the speed is [the same at every time](norm-vel-sq.md), `√(μ / R)`.
