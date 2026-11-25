# A countable bounded-pointwise core of the graph suffices for a martingale problem

Let $E$ be a metric space, $A$ a set of pairs $(f,g)$ of bounded measurable functions on $E$ (for instance the graph of an operator), and let $\mathcal G=\{(f_k,g_k):k\in\mathbb N\}$ be a countable set of pairs of bounded measurable functions such that every $(f,g)\in A$ is the bounded-pointwise limit of a *sequence* in $\mathcal G$: there are $k_1,k_2,\ldots$ with

$$\sup_m\bigl(\lVert f_{k_m}\rVert_\infty+\lVert g_{k_m}\rVert_\infty\bigr)<\infty,\qquad f_{k_m}\to f,\quad g_{k_m}\to g\quad\text{pointwise on }E.$$

Let $X$ be a process with càdlàg paths in $E$, adapted to a filtration $(\mathcal F_t)$, such that for every $k$

$$f_k(X_t)-f_k(X_0)-\int_0^tg_k(X_s)\,ds$$

is an $(\mathcal F_t)$-martingale. Then $f(X_t)-f(X_0)-\int_0^tg(X_s)\,ds$ is an $(\mathcal F_t)$-martingale for every $(f,g)\in A$; so $X$ solves the [martingale problem](martingale-problems-generic-definition.md) for $A$ as soon as it solves it for $\mathcal G$.

For a finite set $E$ with rate matrix $Q$, the rational linear span of $\{(\mathbf 1_i,Q\mathbf 1_i):i\in E\}$ is such a countable set for the graph of $Q$: every $(f,Qf)$ is the uniform limit of $(f^{(m)},Qf^{(m)})$ with $f^{(m)}$ having rational coefficients converging to those of $f$. The finite set $\{(\mathbf 1_i,Q\mathbf 1_i)\}$ alone does not suffice: a sequence from a finite set of functions on a finite set converges pointwise only if it is eventually constant, so it cannot approach $(2\cdot\mathbf 1_i,2Q\mathbf 1_i)$.

## Depends on

- [Martingale problems](martingale-problems-generic-definition.md)

## Proof depends on

- [Conditional expectation](../../foundations/conditional-expectation/README.md)

## Expansion

A full proof page must establish:

- The limit: for $s\le t$ and bounded $\mathcal F_s$-measurable $H$, $\mathbb E\bigl[\bigl(f_{k_m}(X_t)-f_{k_m}(X_s)-\int_s^tg_{k_m}(X_u)\,du\bigr)H\bigr]=0$, and dominated convergence in $\omega$ and in the time integral (joint measurability of $(u,\omega)\mapsto X_u(\omega)$ from càdlàg paths) passes to the limit pair.
- The finite-state example and the failure of the finite generating set.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Ch. 4 (bounded-pointwise closure of generators).
