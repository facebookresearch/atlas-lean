# Moran particle system with bounded mutation on a compact type space

Let $E$ be a compact metric space and $B$ a bounded jump-type mutation generator on $C(E)$, $B f(x) = \int (f(y) - f(x))\, \kappa(x, dy)$, given by a weakly continuous kernel $\kappa$ of total rate at most $\lambda$, as for a [bounded-rate jump Markov process](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/bounded-rate-jump-markov-process-on-a-compact-sp.md). In the Moran system of $N$ particles with types in $E$, each particle mutates independently according to $\kappa$, and for each ordered pair $(i, j)$ of distinct particles, at rate $1/2$, particle $j$ is replaced by a copy of particle $i$. Then:

- the $N$-particle system is a bounded-rate jump process on $E^N$, obtained from the summed kernel of the mutation and resampling jumps;
- its empirical measure $\frac1N \sum_{i=1}^N \delta_{x_i}$ is a càdlàg Markov process on $\mathcal M_1(E)$, with generator $A_N$ acting on the polynomial test functions $\Phi_f(\mu) = \langle f, \mu^{\otimes n} \rangle$, $f \in C(E^n)$.

For finite $E$ the system is a finite-state continuous-time Markov chain. Unbounded Feller mutation, such as Brownian mutation on a circle, is a separate target.

## Depends on

- [Bounded-rate jump Markov process on a compact space by uniformization](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/bounded-rate-jump-markov-process-on-a-compact-sp.md)

## Proof depends on

- [Finite interacting particle systems (graphical construction)](../../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/finite-interacting-particle-systems-graphical-co.md)

## Expansion

A full proof page must still establish:

- the bounded-rate construction on $E^N$ and the Markov property of the empirical measure, by exchangeability of the particle dynamics;
- the formula for $A_N \Phi_f$;
- the finite-type case as a [finite interacting particle system](../../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/finite-interacting-particle-systems-graphical-co.md).

## Sources

- D. A. Dawson, "Measure-valued Markov processes", in *École d'Été de Probabilités de Saint-Flour XXI–1991*, Lecture Notes in Mathematics 1541, Springer, 1993, Moran approximation, <https://link.springer.com/chapter/10.1007/BFb0084190>
