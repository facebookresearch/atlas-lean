# Riemann solution of the Buckley-Leverett equation

This node covers the entropy solution of the Buckley-Leverett injection problem. Let $f : [0, 1] \to [0, 1]$ be smooth and increasing
with $f(0) = 0$, $f(1) = 1$ and $f'(1) < 1$, and suppose $f$ is strictly convex on $[0, s_i]$ and strictly concave on $[s_i, 1]$ for a
single inflection point $s_i \in (0, 1)$. Then $g(s) = s f'(s) - f(s)$ is positive on $(0, s_i]$, strictly decreasing on $[s_i, 1]$ and
negative at $s = 1$, so there is exactly one $s^* \in (s_i, 1)$ with

$$f'(s^*) = \frac{f(s^*)}{s^*} .$$

For the scalar conservation law $s_t + f(s)_x = 0$ with initial data $s = 1$ for $x < 0$ and $s = 0$ for $x > 0$, the entropy solution is
self-similar: $s = 1$ for $x/t \le f'(1)$, a rarefaction with $f'(s) = x/t$ for $f'(1) < x/t < f'(s^*)$, a shock
from $s^*$ to $0$ moving at speed $f(s^*)/s^*$, and $s = 0$ ahead of it.

## Expansion

A good expansion states the S-shaped flux hypotheses precisely, proves existence and uniqueness of the tangency point $s^*$, and
verifies the Rankine-Hugoniot and entropy conditions for the composite wave via the convex hull construction of the flux. The derivation
of the equation from two-phase Darcy flow without capillarity and gravity is a separate node.

## Sources

- R. J. LeVeque, *Finite Volume Methods for Hyperbolic Problems*, Cambridge University Press, 2002, for the Buckley-Leverett equation and nonconvex Riemann problems.
