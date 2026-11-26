# Attractors of two weakly coupled patches with an overcompensating Allee map

**Local dynamics.** Let
$$f(x) = x \exp\Bigl( r\Bigl(1 - \frac{x}{K}\Bigr)\Bigl(\frac{x}{A} - 1\Bigr) \Bigr), \qquad x \ge 0,\quad r > 0,\quad 0 < A < K,$$
a Ricker map with a strong Allee effect: fixed points $0$ (extinction, always stable), the Allee threshold $A$ and the carrying capacity $K$.
For small $r$ the map is bistable (initial densities between $A$ and $\bar A$, where $f(\bar A) = A$, persist); beyond a threshold $r_{th}$ with
$f(f(D)) = A$ ($D$ the critical point of $f$), almost every initial density goes extinct (*essential extinction*).

**Coupled patches.** Two identical patches with dispersal fraction $d \in [0, 1/2]$ after reproduction:
$$x_{t+1} = (1-d) f(x_t) + d f(y_t), \qquad y_{t+1} = (1-d) f(y_t) + d f(x_t),$$
i.e. iteration of $F(x,y) = ((1-d)f(x) + d f(y),\ d f(x) + (1-d) f(y))$ on $[0,\infty)^2$.

**Theorem.** Suppose $f$ has a positive, linearly stable periodic orbit $\{p, f(p), \dots, f^{n-1}(p)\}$ of period $n \ge 1$, and let
$$\mathcal P = \{(0,0), (0,p), (p,0), (p,p), (p, f(p)), \dots, (p, f^{n-1}(p))\},$$
whose forward orbits under the uncoupled map $f \times f$ are its $n + 3$ stable periodic orbits. Let $U$ be an open neighbourhood of
$\bigcup_{i=1}^n (f\times f)^i(\mathcal P)$. Then for all sufficiently small $d > 0$, $F$ has $n+3$ linearly stable periodic orbits in $U$ (continuations of
those of $f \times f$), and almost every initial condition converges to one of them. If moreover $n$ is not a power of $2$, $F$ has infinitely many
unstable periodic orbits.

## Depends on

- [Levins metapopulation on a patch network](../levins-metapopulation-on-a-patch-network/README.md)

## Expansion

At $d = 0$ the stable periodic orbits of $f \times f$ are products of stable orbits of $f$: extinction in both patches, persistence on the cycle
in one patch only (two asymmetric orbits) and the $n$ relative phase shifts of the cycle in both patches. Linearly stable (hyperbolic) periodic
orbits persist under the $C^1$-small perturbation $F - f\times f = O(d)$, and the proof (Appendix B) controls the remaining orbits so that almost every initial
condition is still captured by one of these continuations. Sharkovskii's theorem gives infinitely many periodic orbits of $f$ when it has a period that is not a power of $2$, and
their products remain (unstable) periodic orbits of $F$. Numerically, for larger $d$ fewer than $n+3$ attractors coexist, and dispersal can
rescue a population from essential extinction. (Vortkamp et al. 2020, Equations 1–3, Theorem 1 and Appendix B.)

## Sources

- I. Vortkamp, S. J. Schreiber, A. Hastings, and F. M. Hilker, "Multiple Attractors and Long Transients in Spatially Structured Populations with an Allee Effect", Bulletin of Mathematical Biology (2020), <https://doi.org/10.1007/s11538-020-00750-x> (PMC7295732).
