# Discrete exponential stability bound for minimizing movements

Let $H$ be a real inner product space, $F$ $\lambda$-convex, $h > 0$ with $1 + \lambda h > 0$, and
$(\rho^1_k)$, $(\rho^2_k)$ two [minimizing-movement sequences](../minimizing-movements/is-minimizing-movement.md). Then for
every $k$,

$$(1 + \lambda h)^k \, \|\rho^1_k - \rho^2_k\| \le \|\rho^1_0 - \rho^2_0\|,$$

by iterating the [one-step bound](contraction.md). With $t = kh$, $(1 + \lambda h)^{-k}$ is the
implicit-Euler approximation of the factor $e^{-\lambda t}$ in the exponential stability estimate
$\|\rho^1(t) - \rho^2(t)\| \le e^{-\lambda t} \|\rho^1(0) - \rho^2(0)\|$ of $\lambda$-convex
gradient flows: a contraction when $\lambda > 0$, a nonexpansion when $\lambda = 0$, and an allowed growth
when $\lambda < 0$.

## Sources

- F. Otto, M. Westdickenberg, *Eulerian calculus for the contraction in the Wasserstein distance*, Section 1 (version read: http://www.instmath.rwth-aachen.de/~mwest/files/OttoWest.pdf).
