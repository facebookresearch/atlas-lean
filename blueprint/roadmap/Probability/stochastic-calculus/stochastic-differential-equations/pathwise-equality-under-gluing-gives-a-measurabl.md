# Pathwise equality under gluing gives a measurable strong-solution functional

Let $\hat P$ be the measure obtained by [gluing two weak solutions](gluing-two-weak-solutions-over-a-common-initial.md) over the common law $\nu$ of $(X_0,B)$, with conditional laws $Q_1,Q_2$ and coordinates $(y_1,y_2,x_0,w)$. If $y_1=y_2$ $\hat P$-almost surely, then there is a jointly measurable map $F:\mathbb R\times W\to W$ such that

$$Q_1(x_0,w;\cdot)=Q_2(x_0,w;\cdot)=\delta_{F(x_0,w)}\qquad\text{for }\nu\text{-almost every }(x_0,w),$$

and hence $y_1=y_2=F(x_0,w)$ $\hat P$-almost surely, and $X^i=F(X^i_0,B^i)$ $P_i$-almost surely for $i=1,2$. No adaptedness or nonanticipation of $F$ is asserted here; that is the [causal version of the strong-solution functional](causal-nonanticipating-version-of-the-strong-sol.md).

## Depends on

- [Gluing two weak solutions over a common initial value and Brownian motion](gluing-two-weak-solutions-over-a-common-initial.md)

## Expansion

The proof rests on a generic measure lemma: if $\mu_1,\mu_2$ are probability measures on a standard Borel space with $(\mu_1\otimes\mu_2)(\{(y,y)\})=1$, then $\mu_1=\mu_2$ is a Dirac mass. Applied for $\nu$-almost every $(x_0,w)$ to $Q_1\otimes Q_2$, it gives the Dirac masses; the atom depends measurably on $(x_0,w)$ on a measurable set of full measure, and $F$ is extended by a constant elsewhere. The transfer to the original spaces uses that the law of $(X^i,X^i_0,B^i)$ is $Q_i\,\nu$.

## Sources

- T. Yamada and S. Watanabe, *On the uniqueness of solutions of stochastic differential equations*, J. Math. Kyoto Univ. 11 (1971), 155–167, main theorem argument.
- Wikipedia contributors, *Yamada–Watanabe theorem*, <https://en.wikipedia.org/wiki/Yamada%E2%80%93Watanabe_theorem>.
