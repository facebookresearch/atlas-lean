# Generalized Eulerian polynomials at $x = -1$, $y = 1$

Let $P_m(q, t; x, y)$ be the
generalized Eulerian polynomial. For a permutation $w$ write $\mathrm{cyc}(w)$ for its number of
cycles (fixed points counted as cycles), $\mathrm{exc}(w)$ for its number of excedances (points
$i$ with $w(i) > i$) and $\mathrm{dexc}(w)$ for its number of double excedances, and let $D_{2n}$
be the set of derangements (permutations without fixed points) of $\{0, 1, \dots, 2n-1\}$. Then
for all rational numbers $q, t$ and every $n \ge 0$, $P_{2n+1}(q, t; -1, 1) = 0$ and

$$
(-1)^n P_{2n}(q, t; -1, 1) = \sum_{w \in D_{2n}} q^{\mathrm{cyc}(w)} (-1)^{n - \mathrm{exc}(w)}
= \sum_{w \in D_{2n},\ \mathrm{exc}(w) = n,\ \mathrm{dexc}(w) = 0} q^{\mathrm{cyc}(w)},
$$

where the exponent $n - \mathrm{exc}(w)$ is an integer, possibly negative.

## Sources

- Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Corollary 8 (`jis-2024-24.1.5-cor-8`).
