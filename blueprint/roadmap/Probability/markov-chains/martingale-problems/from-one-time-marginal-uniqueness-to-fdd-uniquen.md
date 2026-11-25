# Uniqueness of one-time marginals implies uniqueness of finite-dimensional distributions for martingale problems

Let $E$ be a metric space and $A$ a set of pairs $(f,g)$ of bounded measurable functions on $E$, and fix a path class (càdlàg or continuous). Suppose that for every probability measure $\nu$ on $E$, any two solutions of the $(A,\nu)$ [martingale problem](martingale-problems-generic-definition.md) in this path class have the same one-time marginals: $X_t$ and $X'_t$ have the same law for every $t\ge0$. Then, for every $\nu$, any two solutions of the $(A,\nu)$ martingale problem have the same finite-dimensional distributions.

The key step is tilting by the past. Let $X$ solve the $(A,\nu)$ martingale problem with respect to $(\mathcal F_t)$ on $(\Omega,\mathcal F,\mathbb P)$, let $s\ge0$, and let $Z\ge0$ be a bounded $\mathcal F_s$-measurable random variable with $\mathbb E Z>0$. Under $\mathbb Q=(Z/\mathbb EZ)\,\mathbb P$, the shifted process $(X_{s+t})_{t\ge0}$ solves the martingale problem for $A$ with respect to $(\mathcal F_{s+t})_{t\ge0}$, with initial law $\mathbb Q\circ X_s^{-1}$. Applying the hypothesis to the tilted laws and inducting on the number of times $0\le t_1<\cdots<t_r$ gives equality of $\mathbb E\bigl[\prod_{i=1}^rh_i(X_{t_i})\bigr]$ for bounded measurable $h_i\ge0$.

## Depends on

- [Martingale problems](martingale-problems-generic-definition.md)

## Proof depends on

- [General optional stopping for uniformly integrable martingales](../../martingales/optional-stopping-theorem/integral-stopped-value-at-top-eq-of-unif.md)

## Expansion

A full proof page must establish:

- The tilting lemma: for $(f,g)\in A$, $u\le v$ and bounded $\mathcal F_{s+u}$-measurable $H$, $\mathbb E_{\mathbb Q}\bigl[(f(X_{s+v})-f(X_{s+u})-\int_u^vg(X_{s+r})\,dr)H\bigr]=\mathbb E_{\mathbb P}[\,\cdots\,ZH]/\mathbb EZ=0$, since $ZH$ is bounded and $\mathcal F_{s+u}$-measurable; and the shifted process stays in the path class.
- The induction: with $Z=\prod_{i<r}h_i(X_{t_i})$ and $s=t_{r-1}$, both solutions give tilted solutions whose initial laws agree by the induction hypothesis, so their one-time marginals at $t_r-t_{r-1}$ agree; the case $\mathbb EZ=0$ is trivial.
- Equality of the products for all bounded nonnegative $h_i$ determines the finite-dimensional distributions.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Ch. 4 (from one-dimensional to finite-dimensional uniqueness).
