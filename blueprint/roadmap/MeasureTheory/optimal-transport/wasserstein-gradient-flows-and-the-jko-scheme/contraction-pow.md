# Discrete exponential contraction of minimizing movements

Let $H$ be a real inner product space, $F$ $\lambda$-convex, $h > 0$ with $1 + \lambda h > 0$, and
$(\rho^1_k)$, $(\rho^2_k)$ two [minimizing-movement sequences](is-minimizing-movement.md). Then for
every $k$,

$$(1 + \lambda h)^k \, \|\rho^1_k - \rho^2_k\| \le \|\rho^1_0 - \rho^2_0\|,$$

by iterating the [one-step contraction](contraction.md). With $t = kh$, $(1 + \lambda h)^{-k}$ is the
implicit-Euler approximation of the factor $e^{-\lambda t}$ in the contraction
$\|\rho^1(t) - \rho^2(t)\| \le e^{-\lambda t} \|\rho^1(0) - \rho^2(0)\|$ of $\lambda$-convex
gradient flows.

## Sources

- F. Otto, M. Westdickenberg, *Eulerian calculus for the contraction in the Wasserstein distance*, Section 1 (version read: http://www.instmath.rwth-aachen.de/~mwest/files/OttoWest.pdf).
