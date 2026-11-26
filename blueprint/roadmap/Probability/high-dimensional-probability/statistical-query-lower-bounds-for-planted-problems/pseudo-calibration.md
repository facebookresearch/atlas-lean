# Pseudo-calibration for sum-of-squares lower bounds

For a planted problem with null $\mathbb{Q}$ (for example $G(n,1/2)$) and planted distribution $\mathbb{P}$ jointly generating an instance $G$ and a hidden solution $x$ (for example the indicator of a planted clique), the degree-$d$ **pseudo-calibrated pseudo-expectation** assigns to each instance $G$ and each polynomial $q(x)$ of degree at most $d$ the value

$$
\tilde{\mathbb{E}}_G[q] = \sum_{\alpha :\, |\alpha| \le \tau} \widehat{\mathbb{E}_{\mathbb{P}}[q(x) \mid G]}(\alpha)\,\chi_\alpha(G),
$$

the truncation to low-degree characters $\chi_\alpha$ (with respect to $\mathbb{Q}$) of the planted conditional expectation, so that $\mathbb{E}_{G \sim \mathbb{Q}}[\tilde{\mathbb{E}}_G[q]\,\chi_\alpha(G)] = \mathbb{E}_{(G,x) \sim \mathbb{P}}[q(x)\chi_\alpha(G)]$ for all low-degree $\alpha$. It is a candidate dual certificate for the degree-$d$ sum-of-squares relaxation on null instances, valid when the associated moment matrix is positive semidefinite with high probability.

## Depends on

- [The Lasserre / sum-of-squares hierarchy for Boolean polynomial optimization](../../../Logic/proof-theory/sum-of-squares-lower-bounds-and-pseudocalibration/lasserre-hierarchy.md)

## Sources

- B. Barak, S. B. Hopkins, J. Kelner, P. K. Kothari, A. Moitra, A. Potechin, "A Nearly Tight Sum-of-Squares Lower Bound for the Planted Clique Problem", FOCS (2016); SIAM Journal on Computing 48 (2019), arXiv:1604.03084.
