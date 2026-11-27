# Hertz contact of two elastic spheres

This node covers Hertz's solution for frictionless contact of elastic spheres. Let two homogeneous isotropic linearly elastic spheres
of radii $R_1, R_2 > 0$, Young's moduli $E_1, E_2 > 0$ and Poisson ratios $\nu_1, \nu_2 \in (-1, 1/2)$ be pressed together by a normal force
$F > 0$, with the small-strain half-space approximation near the contact. With $1/R = 1/R_1 + 1/R_2$ and
$1/E^* = (1 - \nu_1^2)/E_1 + (1 - \nu_2^2)/E_2$, the contact region is a disc of radius $a$, the pressure on it is
$p(r) = p_0\sqrt{1 - r^2/a^2}$, and

$$a = \left(\frac{3FR}{4E^*}\right)^{1/3}, \qquad p_0 = \frac{3F}{2\pi a^2}, \qquad \delta = \frac{a^2}{R},$$

where $\delta$ is the approach of distant points of the two bodies.

## Expansion

A good expansion states the half-space boundary problem with the unilateral contact conditions, proves that the displayed
pressure produces a surface displacement that is quadratic in $r$ inside the disc (the classical potential computation), and then fixes $a$
and $\delta$ by the gap and force conditions. Elastohydrodynamic contact and wear laws are separate nodes.

## Sources

- K. L. Johnson, *Contact Mechanics*, Cambridge University Press, 1985, for the Hertz theory.
- J. E. Shigley and C. R. Mischke, *Mechanical Engineering Design*, 6th edition, McGraw-Hill, 2001, for contact stresses in machine elements.
