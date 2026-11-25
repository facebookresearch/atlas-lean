# Kepler's equation has a unique solution and gives the time on an elliptic orbit

This node covers Kepler's equation for elliptic two-body motion. For every eccentricity $e \in [0, 1)$ and mean anomaly $M \in \mathbb{R}$
the equation $E - e\sin E = M$ has exactly one solution $E \in \mathbb{R}$; it depends real-analytically on $(M, e)$ and $E - M$ is $2\pi$-periodic
in $M$. For the Kepler problem $\ddot r = -\mu r/|r|^3$, $\mu > 0$, with negative energy, nonzero angular momentum $r \times \dot r \ne 0$ (so the orbit is a
nondegenerate ellipse with eccentricity $e \in [0, 1)$ and semimajor axis $a$), the position in orbital-plane coordinates centered at the attracting
focus with the first axis toward periapsis is $r = a(\cos E - e,\ \sqrt{1 - e^2}\sin E)$, where $E$ solves Kepler's equation with $M = n(t - t_p)$, $n = \sqrt{\mu/a^3}$ and $t_p$ a
time of periapsis passage.

## Expansion

A good expansion proves existence and uniqueness from strict monotonicity of $E \mapsto E - e\sin E$ (its derivative is at least
$1 - e > 0$), analyticity from the implicit function theorem, and then verifies the parametrization against the equations of motion. The
circular case $e = 0$ is included. Parabolic and hyperbolic time equations are separate nodes.

## Sources

- R. R. Bate, D. D. Mueller, J. E. White and W. W. Saylor, *Fundamentals of Astrodynamics*, 2nd edition, Dover, 2020, for Kepler's equation and time of flight.
- J. E. Prussing and B. A. Conway, *Orbital Mechanics*, 2nd edition, Oxford University Press, 2013, for elliptic orbit timing.
