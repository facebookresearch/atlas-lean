# Regular conditional laws of a martingale-problem solution at a stopping time

Let $E$ be a Polish space, $A$ a set of pairs of bounded measurable functions on $E$ with a countable set $\mathcal G=\{(f_k,g_k)\}$ of pairs with $f_k$ bounded continuous and $g_k$ bounded measurable, such that every pair of $A$ is the bounded-pointwise limit of a sequence in $\mathcal G$ ([countable core lemma](countable-bounded-pointwise-graph-core-for-marti.md)). Let $X$ solve the $(A,\mu)$ [martingale problem](martingale-problems-generic-definition.md) with respect to $(\mathcal F_t)$, with continuous paths, and let $\tau$ be an almost surely finite $(\mathcal F_t)$-stopping time. Let $(P_\omega)_{\omega\in\Omega}$ be a regular conditional distribution of the shifted path $(X_{\tau+t})_{t\ge0}\in C([0,\infty),E)$ given $\mathcal F_\tau$. Then for $\mathbb P$-almost every $\omega$, the coordinate process under $P_\omega$ solves the $(A,\delta_{X_\tau(\omega)})$ martingale problem with respect to its natural filtration.

The countable core is what makes this possible: the martingale identities for the countably many pairs $(f_k,g_k)$, rational times and a countable family of test functions of the past hold simultaneously off one $\mathbb P$-null set, and the core lemma extends them to every pair of $A$.

## Depends on

- [A countable bounded-pointwise core of the graph suffices for a martingale problem](countable-bounded-pointwise-graph-core-for-marti.md)
- [Martingale problems](martingale-problems-generic-definition.md)
- [Regular conditional distributions](../../foundations/regular-conditional-distributions/is-regular-conditional-distribution.md)

## Proof depends on

- [Optional stopping theorem in continuous time](../../martingales/optional-stopping-theorem/stopped-value-ae-eq-cond-exp-of-le-of-co.md)

## Expansion

A full proof page must establish:

- Existence of the regular conditional distribution on the Polish path space, and $P_\omega(Y_0=X_\tau(\omega))=1$ for almost every $\omega$.
- For each $k$, rational $0\le u<v$ and each $H$ in a countable family of bounded continuous cylinder functions of the path up to time $u$: optional stopping at the bounded stopping times $(\tau\wedge n)+u\le(\tau\wedge n)+v$ gives $\mathbb E\bigl[\mathbf 1_B\,\mathbb E_{P_\omega}[(f_k(Y_v)-f_k(Y_u)-\int_u^vg_k(Y_r)\,dr)H]\bigr]=0$ for $B\in\mathcal F_\tau$, hence the inner expectation vanishes off a null set.
- Extension to all real times by right-continuity and to the natural filtration by a monotone-class argument, then to $A$ by the core lemma.
- A continuous probe: Brownian motion, $A=\tfrac12f''$ on $C_c^2(\mathbb R)$, at a hitting time. Continuous-time Markov chains need a càdlàg version of the statement, which is not claimed here.

## Sources

- D. W. Stroock and S. R. S. Varadhan, *Multidimensional Diffusion Processes*, Grundlehren 233, Springer (1979), <https://books.google.com/books?id=vKC1BwAAQBAJ> (conditioning at stopping times).
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Ch. 4.
