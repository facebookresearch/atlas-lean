# Yamada–Watanabe theorem: weak existence and pathwise uniqueness

For the one-dimensional equation $dX_t=b(X_t)\,dt+\sigma(X_t)\,dB_t$ with Borel coefficients, with [weak solutions and pathwise uniqueness](gluing-two-weak-solutions-over-a-common-initial.md) as defined there, suppose that pathwise uniqueness holds and that a weak solution exists with initial law $\mu$. Then:

1. uniqueness in law holds: any two weak solutions with $X_0\sim\mu$, on possibly different filtered spaces, have the same law of $(X_0,B,X)$, in particular of $X$;
2. there is a measurable map $F:\mathbb R\times W\to W$, [causal modulo the law of $(X_0,B)$](causal-nonanticipating-version-of-the-strong-sol.md), such that on every filtered probability space satisfying the usual conditions with an $\mathcal F_0$-measurable $\xi\sim\mu$ and an $(\mathcal F_t)$-Brownian motion $B$, the process $F(\xi,B)$ is a strong solution with initial value $\xi$, and every weak solution there with the same $\xi$ and $B$ is indistinguishable from it.

Both follow by gluing two solutions over the common law of $(X_0,B)$ and applying [pathwise equality under gluing](pathwise-equality-under-gluing-gives-a-measurabl.md): the glued solutions coincide, so both equal $F(x_0,w)$.

## Depends on

- [Gluing two weak solutions over a common initial value and Brownian motion](gluing-two-weak-solutions-over-a-common-initial.md)
- [Pathwise equality under gluing gives a measurable strong-solution functional](pathwise-equality-under-gluing-gives-a-measurabl.md)
- [Causal version of the strong-solution functional](causal-nonanticipating-version-of-the-strong-sol.md)

## Expansion

A full page assembles the three lemmas: uniqueness in law because $X^i=F(X^i_0,B^i)$ with the same $F$ and the same law of $(X^i_0,B^i)$, and existence of a strong solution from the causal version. Path spaces are standard Borel throughout. A standard application is [Yamada–Watanabe pathwise uniqueness](yamada-watanabe-pathwise-uniqueness-holder-1-2-d.md), which supplies the pathwise-uniqueness hypothesis for Hölder-$\frac12$ diffusion coefficients.

## Sources

- T. Yamada and S. Watanabe, *On the uniqueness of solutions of stochastic differential equations*, J. Math. Kyoto Univ. 11 (1971), 155–167, main theorem.
- N. Ikeda and S. Watanabe, *Stochastic Differential Equations and Diffusion Processes*, 2nd ed., North-Holland, 1989, <https://books.google.com/books?id=QZbOBQAAQBAJ>, textbook exposition (topic).
- Wikipedia contributors, *Yamada–Watanabe theorem*, <https://en.wikipedia.org/wiki/Yamada%E2%80%93Watanabe_theorem>, section "Theorem".
