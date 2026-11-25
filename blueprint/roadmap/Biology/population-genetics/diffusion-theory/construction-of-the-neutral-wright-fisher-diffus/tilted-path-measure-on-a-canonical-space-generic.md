# Tilted path measure on a canonical space

Let $E$ be a compact metric space, such as $[0, 1]$ or a simplex, and let $Q_x$, $x \in E$, be laws on $C([0, \infty), E)$, measurable in $x$, under which the coordinate process solves the [martingale problem](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md) for an operator $L$ started at $x$; for instance the [laws of a continuous modification](law-of-a-continuous-modification-on-c-0-infinity.md). Let $g \in \mathcal D(L)$ with $g \ge c > 0$, let $Z_t = \frac{g(X_t)}{g(X_0)} \exp\bigl(-\int_0^t \frac{Lg}{g}(X_s)\, ds\bigr)$ be the [exponential martingale](../../../../Probability/markov-chains/martingale-problems/exponential-martingale-for-positive-test-functio.md), and let $(\mathcal F_t)$ be the canonical filtration. Then the measures $Z_t \cdot Q_x$ on $\mathcal F_t$, $t \ge 0$, are consistent and extend to a unique probability measure $Q^g_x$ on the canonical $\sigma$-field with $Q^g_x|_{\mathcal F_t} = Z_t \cdot Q_x$ for every $t$, and $x \mapsto Q^g_x(A)$ is measurable. If $g$ is constant, $Q^g_x = Q_x$.

## Depends on

- [Exponential martingale for positive test functions in a martingale problem](../../../../Probability/markov-chains/martingale-problems/exponential-martingale-for-positive-test-functio.md)
- [Martingale problems (generic definition)](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md)

## Proof depends on

- [Law of a continuous modification on the space of continuous paths, measurable in the initial point](law-of-a-continuous-modification-on-c-0-infinity.md)
- [Extension of consistent measures on the canonical filtration of continuous paths](../../../../Probability/foundations/consistent-measures-on-continuous-path-space.md)

## Expansion

A full proof page must still establish:

- consistency of the family $Z_t \cdot Q_x$ from the martingale property of $Z$;
- the extension to the canonical $\sigma$-field of $C([0, \infty), E)$ and its uniqueness;
- measurability in $x$, and the constant case.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 4, Section 3 (change of measure), <https://doi.org/10.1002/9780470316658>
