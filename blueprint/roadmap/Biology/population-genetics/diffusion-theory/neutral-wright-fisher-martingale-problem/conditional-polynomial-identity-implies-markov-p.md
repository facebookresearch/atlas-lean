# A conditional polynomial identity implies the Markov property and uniqueness in law

Let $E$ be a compact metric space on which the polynomials are dense in $C(E)$, such as $[0, 1]$ or a simplex, and let $(T_t)_{t \ge 0}$ be a Markov semigroup of positive operators on $C(E)$: $T_t 1 = 1$, $T_0 = I$ and $T_{s+t} = T_s T_t$ for all $s, t \ge 0$ (so each $T_t$ is a contraction). Let $X$ be an $E$-valued process adapted to a filtration $(\mathcal F_t)$ such that, for every polynomial $p$ and all $s \le t$,

$$\mathbb E[p(X_t) \mid \mathcal F_s] = (T_{t-s} p)(X_s) \quad \text{almost surely}.$$

Then the same identity holds for every $f \in C(E)$, by density and the contraction property; $X$ is a Markov process with respect to $(\mathcal F_t)$ with transition operators $(T_t)$; and the finite-dimensional laws of $X$ are determined by the law of $X_0$ and $(T_t)$, by iterated conditioning. Hence two processes satisfying the identity with the same initial law have the same law on path space. The argument uses neither the general uniqueness theorem for martingale problems by duality nor a disintegration. It applies with the semigroup obtained from $T_t = e^{tA}$ on polynomials, given by the [conditional polynomial-semigroup identity](conditional-polynomial-semigroup-identity-for-ma.md), and with random initial laws.

## Depends on

- [Conditional expectation given a σ-field](../../../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md)

## Proof depends on

- [Conditional polynomial-semigroup identity for martingale-problem solutions with triangular generators](conditional-polynomial-semigroup-identity-for-ma.md)
- [Martingale problems (generic definition)](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md)
- [Tower property of conditional expectation](../../../../Probability/foundations/conditional-expectation/tower-property/tower-property.md)

## Expansion

A full proof page must still establish:

- the extension from polynomials to $C(E)$;
- the finite-dimensional identity, first for two times and then by induction;
- the uniqueness statement, including random initial laws.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 4, Section 1 (Markov processes and transition functions), <https://doi.org/10.1002/9780470316658>
