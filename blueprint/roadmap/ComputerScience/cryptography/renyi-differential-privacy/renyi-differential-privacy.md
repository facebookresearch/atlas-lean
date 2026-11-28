# Rényi divergence and Rényi differential privacy

For probability laws $P$ and $Q$, the [Rényi divergence](../../../InformationTheory/information-inequalities/r-nyi-divergence/renyi-div.md)
at a real order $\alpha > 1$ is $D_\alpha(P \Vert Q) = (\alpha-1)^{-1}\log\int (dP/dQ)^\alpha\,dQ$
when $P \ll Q$, and $\infty$ otherwise. A probability-valued mechanism $M$ is
*$(\alpha, \varepsilon)$-Rényi differentially private* with respect to an adjacency relation
$\mathrm{Adj}$ if $D_\alpha(M(x) \Vert M(y)) \le \varepsilon$ whenever $\mathrm{Adj}(x,y)$.
Outside probability-valued outputs the predicate asserts only the inequality, not a privacy
guarantee. It does not model the orders $1$ and $\infty$.

## Finite-output case

For probability mass functions $P$ and $Q$ on a finite set, when the support of $P$ is contained
in that of $Q$, the integral is a sum over the support of $P$:

$$
D_\alpha(P \Vert Q) = \frac{1}{\alpha - 1}\log \sum_{r : P(r) > 0} P(r)^{\alpha} Q(r)^{1-\alpha} = \frac{1}{\alpha-1}\log \mathbb{E}_{r \sim P}\Bigl[\bigl(P(r)/Q(r)\bigr)^{\alpha-1}\Bigr].
$$

The sum is the order-$\alpha$ *Rényi moment*, the moment generating function of the privacy loss
$\log(P(r)/Q(r))$ at $\alpha-1$. See [the finite-output privacy predicate](is-rdp.md) for the
formulation with support inclusion and nonnegative budget.

## Background

- [Differential privacy](../differential-privacy/differentially-private.md): the original privacy notion on neighbouring databases.

## Sources

- I. Mironov, *Rényi Differential Privacy*, IEEE CSF, 2017, Definitions 3–4 in [arXiv:1702.07476v3](https://arxiv.org/abs/1702.07476v3).
