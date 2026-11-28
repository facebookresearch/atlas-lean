# The one-cycle versus two-cycle conjecture

The one-versus-two-cycle problem asks, given an $n$-vertex graph promised to be either a single cycle of length $n$ or a disjoint union of two cycles of length $n/2$, to decide which case holds. The one-versus-two-cycle conjecture states that every MPC algorithm with strongly sublinear local memory $S = n^{\alpha}$, $\alpha < 1$, and total memory $\mathrm{poly}(n)$, solving this problem requires $\Omega(\log n)$ rounds. The conjecture is open; with machine memory $s$ and polynomially many machines, any round lower bound asymptotically larger than $\Theta(\log_s n)$ for a function in $\mathrm{P}$ would separate $\mathrm{NC}^1$ from $\mathrm{P}$, and for $s = n^{\alpha}$ this already applies to any superconstant lower bound.

## Depends on

- [The massively parallel computation model](massively-parallel-computation-model.md)

## Sources

- T. Roughgarden, S. Vassilvitskii, J. R. Wang, "Shuffles and Circuits (On Lower Bounds for Modern Parallel Computation)", Journal of the ACM 65(6) (2018); SPAA 2016, Theorem 6.1.
- M. Ghaffari, F. Kuhn, J. Uitto, "Conditional Hardness Results for Massively Parallel Computation from Distributed Lower Bounds", FOCS 2019.
