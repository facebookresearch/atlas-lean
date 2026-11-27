# The best linear predictor need not be the conditional expectation

Let $X, Y$ be square-integrable real random variables with $\operatorname{Var}(X) > 0$. The affine function $a + bX$ minimizing $E[(Y - a - bX)^2]$ has $b = \operatorname{Cov}(X, Y)/\operatorname{Var}(X)$ and $a = E[Y] - b E[X]$. It equals the conditional expectation $E[Y \mid X]$ almost surely if and only if $E[Y \mid X]$ is almost surely an affine function of $X$. For example, if $X$ is uniform on $\{-1, 0, 1\}$ and $Y = X^2$, then $\operatorname{Cov}(X, Y) = E[X^3] = 0$, so the best linear predictor is the constant $E[Y] = 2/3$, while $E[Y \mid X] = X^2$.

Proof. In $L^2$, $E[Y \mid X]$ is the orthogonal projection of $Y$ onto the closed subspace of $\sigma(X)$-measurable variables, and the affine functions of $X$ form a closed subspace of it. Projecting first onto the larger subspace and then onto the smaller one gives the projection onto the smaller one, so the best linear predictor is the projection of $E[Y \mid X]$ onto the affine functions of $X$, which equals $E[Y \mid X]$ exactly when $E[Y \mid X]$ already lies in that subspace. The normal equations $E[Y - a - bX] = 0$ and $E[(Y - a - bX)X] = 0$ give $a$ and $b$.

## Expansion

A good expansion adds a page for each pending prerequisite below.

- Proof prerequisite: for square-integrable $Y$ and a sub-σ-field $\mathcal F$, $E[Y \mid \mathcal F]$ is the orthogonal projection of $Y$ onto the closed subspace $L^2(\mathcal F)$, that is, the $\mathcal F$-measurable square-integrable variable minimizing $E[(Y - Z)^2]$.

## Background

- [Conditional expectation](conditional-expectation-given-a-sigma-field/conditional-expectation.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 4.1.15 and the remark after it: for $EX^2 < \infty$, $E(X \mid \mathcal F)$ minimizes $E(X - Y)^2$ over $\mathcal F$-measurable $Y$ and is the projection of $X$ onto $L^2(\mathcal F)$ (p. 213 of the author's January 2019 PDF). The best-linear-predictor characterization and the example are derived above.
