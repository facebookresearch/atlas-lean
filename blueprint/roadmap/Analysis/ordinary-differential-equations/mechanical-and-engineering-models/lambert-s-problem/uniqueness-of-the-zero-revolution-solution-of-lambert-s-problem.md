# Uniqueness of the zero-revolution solution of Lambert's problem

This node covers the solvability of Lambert's two-point boundary-value problem. Let $\mu > 0$, let $r_1, r_2 \in \mathbb{R}^3$ be nonzero and
not collinear, and fix one of the two senses of motion in the plane they span, so that the transfer angle $\Delta\nu \in (0, 2\pi)$ is
determined. Then for every $t > 0$ there is exactly one solution of $\ddot r = -\mu r/|r|^3$ that is at $r_1$ at time $0$ and first reaches
$r_2$ at time $t$ after sweeping the angle $\Delta\nu$ in that sense (a transfer of less than one revolution); it is an elliptic, parabolic or
hyperbolic arc according as $t$ is greater than, equal to or less than the parabolic transfer time determined by $|r_1|$, $|r_2|$ and the chord.

## Expansion

A good expansion states Lambert's theorem that the transfer time depends only on $|r_1| + |r_2|$, the chord and the semimajor axis,
parametrizes the zero-revolution family by one variable across the elliptic, parabolic and hyperbolic cases, and proves that the transfer time
is strictly monotone along it. Multi-revolution branches, orbit determination and patched-conic error bounds are separate nodes.

## Sources

- J. E. Prussing and B. A. Conway, *Orbital Mechanics*, 2nd edition, Oxford University Press, 2013, for Lambert's problem.
- R. R. Bate, D. D. Mueller, J. E. White and W. W. Saylor, *Fundamentals of Astrodynamics*, 2nd edition, Dover, 2020, for the Gauss and Lambert problems.
