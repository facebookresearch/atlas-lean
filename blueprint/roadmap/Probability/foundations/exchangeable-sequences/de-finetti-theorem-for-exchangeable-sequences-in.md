# de Finetti's theorem for exchangeable sequences in a standard Borel space

Let $S$ be a standard Borel space and $X=(X_1,X_2,\ldots)$ an infinite sequence of $S$-valued random variables on a probability space $(\Omega,\mathcal F,\mathbb P)$. Suppose $X$ is exchangeable: for every permutation $\pi$ of $\{1,2,\ldots\}$ that moves only finitely many points, $(X_{\pi(1)},X_{\pi(2)},\ldots)$ has the same law as $X$. Let $\mathcal T=\bigcap_n\sigma(X_n,X_{n+1},\ldots)$ be the tail $\sigma$-algebra. Then:

1. There is a random probability measure $\Lambda$ on $S$, that is, a $\mathcal T$-measurable map from $\Omega$ to the space of probability measures on $S$ with its usual $\sigma$-algebra, such that $X$ is conditionally independent and identically distributed given $\mathcal T$ with directing law $\Lambda$: for every $n$ and all Borel sets $B_1,\ldots,B_n\subseteq S$,

    $$\mathbb P(X_1\in B_1,\ldots,X_n\in B_n\mid\mathcal T)=\prod_{i=1}^n\Lambda(B_i)\qquad\text{almost surely}.$$

    $\Lambda$ is almost surely unique, and $\Lambda=\mathbb P(X_1\in\cdot\mid\mathcal T)$ as a regular conditional distribution.
2. For any Polish topology on $S$ that generates its Borel $\sigma$-algebra, the empirical measures converge weakly to $\Lambda$ almost surely:

    $$\frac1n\sum_{i=1}^n\delta_{X_i}\Longrightarrow\Lambda\qquad\text{almost surely.}$$

Clause 1 needs only the standard Borel structure; clause 2 needs the choice of a compatible Polish topology.

## Proof depends on

- [De Finetti's theorem for binary sequences](../de-finetti-theorem/de-finetti-binary.md)
- [Regular conditional distributions](../regular-conditional-distributions/is-regular-conditional-distribution.md)
- [General optional stopping for uniformly integrable martingales](../../martingales/optional-stopping-theorem/integral-stopped-value-at-top-eq-of-unif.md)

## Expansion

A full proof page must establish the following.

- Existence of the regular conditional distribution $\Lambda=\mathbb P(X_1\in\cdot\mid\mathcal T)$, using that $S$ is standard Borel.
- Conditional independence: for bounded measurable $f_1,\ldots,f_n$, $\mathbb E[\prod_if_i(X_i)\mid\mathcal T]=\prod_i\int f_i\,d\Lambda$, by reverse martingale convergence of symmetrized averages $\binom Nn^{-1}\sum f_1(X_{j_1})\cdots f_n(X_{j_n})$ over distinct indices, or by the Hewitt–Savage route through the exchangeable $\sigma$-algebra, which coincides with $\mathcal T$ up to null sets.
- Clause 2: for each $f$ in a countable convergence-determining class of bounded continuous functions, $\frac1n\sum_{i\le n}f(X_i)\to\int f\,d\Lambda$ almost surely, by the conditional strong law; then intersect the countably many almost-sure events.
- The binary specialization: for $S=\{0,1\}$, $\Lambda=\mathrm{Bernoulli}(P)$ with $P$ the limiting frequency, and integrating clause 1 gives [de Finetti's theorem for binary sequences](../de-finetti-theorem/de-finetti-binary.md) with mixing measure the law of $P$.

## Sources

- O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Springer (2021), <https://link.springer.com/book/10.1007/978-3-030-61871-1>, exchangeability chapter (statement and proof).
