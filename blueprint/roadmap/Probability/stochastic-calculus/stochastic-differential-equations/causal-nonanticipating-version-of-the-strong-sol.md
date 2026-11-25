# Causal version of the strong-solution functional

Assume pathwise uniqueness for $dX_t=b(X_t)\,dt+\sigma(X_t)\,dB_t$, let $\nu$ be the law of $(X_0,B)$ for a weak solution, and let $F:\mathbb R\times W\to W$ be the measurable map with $X=F(X_0,B)$ almost surely given by [pathwise equality under gluing](pathwise-equality-under-gluing-gives-a-measurabl.md), applied to the [glued measure](gluing-two-weak-solutions-over-a-common-initial.md) of the solution with itself. Then $F$ is causal modulo $\nu$: for every $t\ge0$, the map $(x_0,w)\mapsto F(x_0,w)|_{[0,t]}$ is measurable with respect to the $\nu$-completion of $\sigma(x_0,w|_{[0,t]})$.

Consequently, let $(\Omega',\mathcal A',P',(\mathcal F'_t))$ be a filtered probability space whose filtration satisfies the usual conditions (complete and right-continuous), let $\xi$ be $\mathcal F'_0$-measurable, and let $B'$ be an $(\mathcal F'_t)$-Brownian motion such that $(\xi,B')$ has law $\nu$. Then $X'=F(\xi,B')$ is $(\mathcal F'_t)$-adapted and is a strong solution with $X'_0=\xi$. Transfer to target filtrations that are not complete is not asserted; such a filtration is first replaced by its [usual augmentation](../../martingales/stopping-times-and-martingale-problems/martingales-and-martingale-problems-are-preserve.md).

## Depends on

- [Gluing two weak solutions over a common initial value and Brownian motion](gluing-two-weak-solutions-over-a-common-initial.md)
- [Pathwise equality under gluing gives a measurable strong-solution functional](pathwise-equality-under-gluing-gives-a-measurabl.md)

## Proof depends on

- [Regular conditional distributions](../../foundations/regular-conditional-distributions/is-regular-conditional-distribution.md)
- [Martingales and martingale problems are preserved by the usual augmentation](../../martingales/stopping-times-and-martingale-problems/martingales-and-martingale-problems-are-preserve.md)

## Expansion

A full proof uses that, in the glued construction, $Q(x_0,w;A)$ is measurable for the completion of $\sigma(x_0,w|_{[0,t]})$ whenever $A\in\sigma(y|_{[0,t]})$, together with $Q=\delta_{F}$, to obtain the causal measurability of $F|_{[0,t]}$. The transfer uses completeness of $\mathcal F'_t$ to absorb the $\nu$-null modification, and the equality of the laws of $(\xi,B',X')$ and $(X_0,B,X)$ to transfer the integral equation. It should exhibit the guard: on $[0,T]$, the map $F(w)_t=w_T$ for $t<T$ is measurable but anticipating, and is excluded by the conclusion.

## Sources

- T. Yamada and S. Watanabe, *On the uniqueness of solutions of stochastic differential equations*, J. Math. Kyoto Univ. 11 (1971), 155–167, main theorem argument.
- N. Ikeda and S. Watanabe, *Stochastic Differential Equations and Diffusion Processes*, 2nd ed., North-Holland, 1989, <https://books.google.com/books?id=QZbOBQAAQBAJ>, exposition (topic).
