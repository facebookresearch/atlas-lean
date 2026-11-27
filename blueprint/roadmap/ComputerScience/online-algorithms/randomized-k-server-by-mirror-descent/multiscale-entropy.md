# Multiscale entropy regularizer

Let $T = (V, E)$ be an HST in the vertex-weighted form, with root $r$, vertex weights $w_u$ nonincreasing along root-leaf paths and leaf metric $d(\ell, \ell') = w_{\mathrm{lca}(\ell, \ell')}$, leaf set $L$, and $N_u$ leaves below each vertex $u$; write $\chi(u) = \{(v, j) : (u, v) \in E,\ j \in [N_v]\}$. Bubeck, Cohen, Lee, Lee and Mądry represent fractional $k$-server states by points of the *assignment polytope*

$$
A = \Big\{x \in [0, 1]^{\Lambda} : \sum_{i \le |S|} x_{u,i} \le \sum_{(v, j) \in S} x_{v,j} \text{ for all } u \in V,\ S \subseteq \chi(u);\quad x_{r,i} = \mathbf{1}\{i > k\} \text{ for all } i\Big\},
$$

with coordinates $x_{u,i}$ for $u \in V$ and $i \in [N_u]$; for a shift $\delta > 0$ the associated server mass below $u$ is $z_u = \frac{1}{1-\delta}\sum_{i} (1 - x_{u,i})$. The *shifted multiscale entropy* is

$$
\Phi(x) = \sum_{u \in V} w_u \sum_{i \ge 1} (x_{u,i} + \delta) \log (x_{u,i} + \delta).
$$

Each vertex contributes an entropy of its coordinates weighted by its scale $w_u$, and the shift keeps the gradient bounded: $\sup_{x \in A} \|\nabla \Phi(x)\|_{\ell_\infty(1/w)} = O(\log(1/\delta))$. The $k$-server algorithm takes $\delta = \frac{1}{2k}$.

## Depends on

- [Fractional k-server on a tree](fractional-k-server-polytope.md)
- [Bregman divergence (prox-function) of a distance-generating function](../../../Analysis/convex-analysis-and-variations/mirror-descent/bregman.md)

## Sources

- Sébastien Bubeck, Michael B. Cohen, Yin Tat Lee, James R. Lee, Aleksander Mądry, "k-Server via Multiscale Entropic Regularization", STOC (2018), arXiv:1711.01085, Section 3.2.
