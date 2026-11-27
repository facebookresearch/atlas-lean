# Existence and uniqueness of a premixed flame traveling wave with an ignition temperature

This node covers the traveling-wave problem of the one-dimensional premixed flame with unit Lewis number. Let
$f : [0, 1] \to [0, \infty)$ be Lipschitz with $f = 0$ on $[0, \theta_i]$ for some ignition temperature $\theta_i \in (0, 1)$, $f > 0$ on
$(\theta_i, 1)$ and $f(1) = 0$. Then there are exactly one speed $c > 0$ and, up to translation, exactly one profile $\theta \in C^2(\mathbb{R})$
with

$$\theta'' + c\,\theta' + f(\theta) = 0, \qquad \theta(-\infty) = 1, \quad \theta(+\infty) = 0,$$

and this profile is strictly decreasing.

## Expansion

A good expansion reduces the unit-Lewis-number thermal-diffusive model to this scalar equation, then proves existence and
uniqueness of the heteroclinic connection by a phase-plane shooting argument in $c$, using monotonicity of the trajectory leaving the
saddle at $\theta = 1$ in the speed parameter. Stability of the front, unequal Lewis numbers and detonation structure are separate nodes.

## Sources

- Ya. B. Zeldovich, G. I. Barenblatt, V. B. Librovich and G. M. Makhviladze, *The Mathematical Theory of Combustion and Explosions*, Plenum, 1985.
- J. M. Roquejoffre and D. Terman, The asymptotic stability of a traveling wave solution arising from a combustion model, *Nonlinear Analysis* 22 (1994) 1263-1282.
