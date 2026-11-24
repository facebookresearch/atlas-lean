# Concave expected utility prefers the mean of a lottery

Let $u : I \to \mathbb{R}$ be concave on an interval $I$ (for example a CRRA utility on $(0, \infty)$), and let $X$ be an integrable lottery with values in $I$ such that $u(X)$ is integrable. Then $E[u(X)] \le u(E[X])$, so an expected-utility maximizer with utility $u$ weakly prefers receiving $E[X]$ for sure to facing $X$; monotonicity of $u$ is not needed for this. If $u$ is strictly concave and $X$ is not almost surely constant, the inequality is strict.

## Proof depends on

- [Jensen's inequality](../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md): the inequality.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Jensen's inequality for a concave function defined only on an interval, for integrable variables with values in that interval (an adapter from the inequality for functions on all of $\mathbb{R}$).
- Strict Jensen inequality for strictly concave functions and nondegenerate integrable variables.
