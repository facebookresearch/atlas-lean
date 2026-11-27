# Cochains and the coboundary operator over F_2

Let $X$ be a pure $d$-dimensional weighted complex. An **$i$-cochain** over $\mathbb{F}_2$ is a function $f : X(i) \to \mathbb{F}_2$; write $C^i = C^i(X; \mathbb{F}_2)$. The **coboundary operator** $\delta_i : C^i \to C^{i+1}$ is

$$
(\delta_i f)(\sigma) = \sum_{\tau \subset \sigma,\ |\tau| = |\sigma| - 1} f(\tau) \pmod 2.
$$

It satisfies $\delta_{i+1}\delta_i = 0$. The **cocycles** are $Z^i = \ker \delta_i$, the **coboundaries** are $B^i = \operatorname{im} \delta_{i-1}$, and $H^i = Z^i / B^i$ is the $i$-th cohomology. The **weighted norm** of a cochain is $\|f\| = \Pr_{\sigma \sim \Pi_i}[f(\sigma) \ne 0]$.

## Depends on

- [Pure weighted simplicial complexes and their face distributions](../local-spectral-high-dimensional-expanders/pure-weighted-complex.md)
- [Simplicial boundary matrix](../rational-homology-of-simplicial-complexes/boundary-matrix.md)

## Sources

- N. Linial, R. Meshulam, "Homological connectivity of random 2-complexes", Combinatorica 26 (2006) 475-487.
- M. Gromov, "Singularities, expanders and topology of maps. Part 2: from combinatorics to topology via algebraic isoperimetry", Geometric and Functional Analysis 20 (2010) 416-526.
- T. Kaufman, D. Kazhdan, A. Lubotzky, "Ramanujan complexes and bounded degree topological expanders", FOCS (2014); Geometric and Functional Analysis 26 (2016), arXiv:1408.6351.
