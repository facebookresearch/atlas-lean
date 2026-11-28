# The degree-d SoS relaxation of the clique number

For a graph $G$ on vertex set $[n]$, the **degree-$d$ SoS clique relaxation** is

$$
\mathrm{SoS}_d(G) = \max \Bigl\{\, \tilde{\mathbb{E}}\Bigl[\sum_{i} x_i\Bigr] \Bigr\}
$$

over degree-$d$ pseudo-expectations on $\{0,1\}^n$ satisfying $x_i x_j = 0$ for every non-edge $\{i, j\}$ of $G$. It is an upper bound on the clique number $\omega(G)$. In the planted clique problem one asks to distinguish $G \sim G(n, 1/2)$ from $G(n,1/2)$ with a planted clique of size $k$; degree-$d$ SoS succeeds if $\mathrm{SoS}_d(G) < k$ with high probability for $G \sim G(n, 1/2)$.

## Depends on

- [The Lasserre / sum-of-squares hierarchy for Boolean polynomial optimization](lasserre-hierarchy.md)
- [Planted clique model, search and detection problems](../../../GraphTheory/random-graphs/planted-clique/planted-clique-model.md)

## Sources

- R. Meka, A. Potechin, A. Wigderson, "Sum-of-squares lower bounds for planted clique", STOC (2015), arXiv:1503.06447.
- B. Barak, S. B. Hopkins, J. Kelner, P. K. Kothari, A. Moitra, A. Potechin, "A nearly tight sum-of-squares lower bound for the planted clique problem", FOCS (2016); SIAM Journal on Computing 48 (2019), arXiv:1604.03084.
