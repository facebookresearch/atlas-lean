# Vertical Andronov–Hopf bifurcation in the lifted Lotka–Volterra–Autocatalator

**Setting.** The **lifted LVA family** consists of three-species, three-reaction mass-action networks
obtained from the generalized Lotka–Volterra–Autocatalator (which contains the quadratic
autocatalytic step $2X \to 3X$) by adding a species $Z$ without changing the rank; the case $d = 1$ is
the lifted LVA, the only trimolecular member. Its mass-action dynamics satisfy $\dot y = \dot z$, so the
stoichiometric classes are the planes $z = y + C$, and with rate constants
$\kappa_1, \kappa_2, \kappa_3 > 0$ and integer $d \ge 1$ the restriction to a class is the planar
Lotka–Volterra system

$$\dot x = x(\kappa_1 x - \kappa_2 y), \qquad \dot y = y\big(d\kappa_2 x - \kappa_3 (y + C)\big).$$

Its positive equilibria form the ray $\{(t,\ \tfrac{\kappa_1}{\kappa_2} t,\ \tfrac{d\kappa_2}{\kappa_3} t) : t > 0\}$.

**Statement.** The coordinates $v = y/x$, $w = 1/x$ (with time rescaled by $w$) give the
predator–prey system

$$\dot v = v\big((d\kappa_2 - \kappa_1) + (\kappa_2 - \kappa_3) v - \kappa_3 C w\big), \qquad \dot w = w(-\kappa_1 + \kappa_2 v),$$

which has a positive equilibrium if and only if $C$ and $d\kappa_2^2 - \kappa_1\kappa_3$ have the same
sign. For $C > 0$ and $d\kappa_2^2 > \kappa_1\kappa_3$, the function

$$V(v, w) = \kappa_2(v - \bar v \log v) + \kappa_3 C (w - \bar w \log w)$$

is convex with unique minimum at the equilibrium $(\bar v, \bar w)$ and satisfies
$\dot V = \kappa_2(\kappa_2 - \kappa_3)(v - \bar v)^2$. Therefore the positive equilibrium is globally
asymptotically stable for $\kappa_2 < \kappa_3$, a global centre for $\kappa_2 = \kappa_3$, and a global
repellor for $\kappa_2 > \kappa_3$. Provided $\kappa_1 < d\kappa_2$, the family undergoes a **vertical
Andronov–Hopf bifurcation** as $\kappa_2/\kappa_3$ passes through $1$, simultaneously in every
stoichiometric class with $C > 0$: a two-parameter family of periodic orbits exists exactly at
$\kappa_2 = \kappa_3$, and isolated periodic orbits never occur. In the remaining cases ($C = 0$: a line
of equilibria; $C < 0$: a saddle) there is no periodic orbit.

## Expansion

The map $(x,y)\mapsto(y/x, 1/x)$ is a diffeomorphism of the open quadrant, and multiplying the vector
field by $w > 0$ only reparametrizes time, so orbits and their stability are preserved. In the new
coordinates the system is Lotka–Volterra with prey self-interaction coefficient
$\kappa_2 - \kappa_3$, and the classical Volterra function $V$ turns that coefficient into the sign of
$\dot V$. A vertical Hopf bifurcation is the degenerate case in which a complex pair of eigenvalues
crosses the imaginary axis and, at the critical parameter, a whole family of periodic orbits (a centre)
appears instead of a limit cycle; this is the third oscillation mechanism, beside the
Lotka and Ivanova centres, in three-reaction trimolecular quadratic networks.

## Sources

- M. Banaji, B. Boros, J. Hofbauer, "Oscillations in three-reaction quadratic mass-action systems", Studies in Applied Mathematics (2024), <https://doi.org/10.1111/sapm.12639> (PMC10953466). Section 5.2 (lifted LVA family, Eqs. (24)–(26)), Section 4.2 (generalized LVA), Lemma 6.
