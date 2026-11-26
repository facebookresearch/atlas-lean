# Pseudocalibration of pseudo-expectations

Let $\nu$ be a null distribution (e.g. $G(n, 1/2)$) and $\mu$ a planted distribution on pairs $(G, x)$ where $x$ is a hidden solution (e.g. the indicator of a random $k$-clique planted in $G$). For a truncation degree $\tau$ and SoS degree $d$, the **pseudocalibrated pseudo-expectation** is defined for every input $G$ and every monomial $x^{S}$, $|S| \le d$, by

$$
\tilde{\mathbb{E}}_G[x^S] = \sum_{\substack{T \subseteq \binom{[n]}{2} \\ |T| \le \tau}} \mathbb{E}_{(G', x) \sim \mu}\bigl[x^{S} \chi_T(G')\bigr]\, \chi_T(G),
$$

where $\chi_T$ are the Fourier characters of $\nu$. It is the low-degree projection of the planted posterior moments, so that $\mathbb{E}_{G \sim \nu}\,\tilde{\mathbb{E}}_G[x^S \cdot f(G)] = \mathbb{E}_{\mu}[x^S f(G)]$ for every low-degree test function $f$.

## Depends on

- [The degree-d SoS relaxation of the clique number](planted-clique-sos-value.md)

## Sources

- B. Barak, S. B. Hopkins, J. Kelner, P. K. Kothari, A. Moitra, A. Potechin, "A nearly tight sum-of-squares lower bound for the planted clique problem", FOCS (2016); SIAM Journal on Computing 48 (2019), arXiv:1604.03084.
- S. B. Hopkins, "Statistical inference and the sum of squares method", PhD thesis, Cornell University (2018).
