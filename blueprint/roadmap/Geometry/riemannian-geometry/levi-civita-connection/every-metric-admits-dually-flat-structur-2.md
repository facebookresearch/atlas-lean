# Not every Riemannian metric admits a dually flat structure

This result refutes the proposition stated as [Amari's question: does every metric admit a dually flat structure?](every-metric-admits-dually-flat-structur.md). The answer is negative: it is not the case that for every $n \in \mathbb{N}$, every open set $U \subseteq \mathbb{R}^n$ and every matrix-valued function $g = (g_{ij})$ on $\mathbb{R}^n$ whose entries are $C^\infty$ on $U$ and with $g(x)$ positive definite for every $x \in U$, there is a $(0,3)$-tensor field $T = (T_{ijk})$ on $\mathbb{R}^n$ such that

- every entry $T_{ijk}$ is $C^\infty$ on $U$;
- $T$ is totally symmetric at every point: $T_{ijk} = T_{jik} = T_{ikj}$;
- for every $x \in U$ and all indices, both connections

$$\nabla:\ \Gamma^k_{ij} - \tfrac{1}{2} \sum_l g^{kl} T_{ijl}, \qquad \nabla^*:\ \Gamma^k_{ij} + \tfrac{1}{2} \sum_l g^{kl} T_{ijl}$$

have vanishing curvature $R^l_{\ kij}(x) = 0$. Here $\Gamma^k_{ij}$ are the Christoffel symbols of the Levi-Civita connection of $g$ and $g^{kl}$ are the entries of $g^{-1}$.

In other words, not every Riemannian metric on an open subset of $\mathbb{R}^n$ admits such a dually flat structure $(g, \nabla, \nabla^*)$ built from a symmetric cubic tensor.

## Sources

- H. Furuhata, H. Matsuzoe and H. Urakawa, Open problems in affine differential geometry and related topics, Interdiscip. Inform. Sci. 4 (1998), no. 2, item 1(c) (S. Amari).
- S. Amari and J. Armstrong, Curvature of Hessian manifolds, Differential Geom. Appl. 33 (2014), 1–12, Theorem 1. https://doi.org/10.1016/j.difgeo.2014.01.001
