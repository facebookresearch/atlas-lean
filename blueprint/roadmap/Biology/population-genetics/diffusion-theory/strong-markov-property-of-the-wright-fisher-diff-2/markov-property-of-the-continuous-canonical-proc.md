# Markov property of a continuous canonical process with Chapman–Kolmogorov kernels

Let $E$ be a compact metric space and $(K_t)_{t \ge 0}$ a family of Markov kernels on $E$ satisfying the Chapman–Kolmogorov equations and the Feller property, $K_t g \in C(E)$ for $g \in C(E)$. Let $X$ be a continuous modification of the canonical process under the path measure built from $(K_t)$, agreeing with the coordinates at each fixed time, with natural filtration $(\mathcal{F}_t)$. Then for $s \le t$ and every $g \in C(E)$,

$$\mathbb{E}\bigl[g(X_t) \mid \mathcal{F}_s\bigr] = (K_{t-s}\, g)(X_s) \qquad \text{almost surely}.$$

## Depends on

- [Conditional expectation given a σ-field](../../../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md)
- [Path-space measure of a Markov semigroup](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/path-measure.md)

## Proof depends on

- [Filtrations and stopping times](../../../../Probability/martingales/stopping-times-and-martingale-problems/filtrations-and-stopping-times.md)
- [Uniqueness of the conditional expectation](../../../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/ae-eq-cond-exp-of-forall-set-integral-eq.md)

## Expansion

1. The identity on the π-system of cylinder events at finitely many times up to $s$, from the law of the finite chain obtained by adding the time $t$ to the list of times.
2. Extension to $\mathcal{F}_s$ by the π–λ theorem, using that $X$ agrees with the coordinates at fixed times.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 4, Section 1.
