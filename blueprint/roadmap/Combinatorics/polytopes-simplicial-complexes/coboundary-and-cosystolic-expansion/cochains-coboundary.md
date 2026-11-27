# Cochains and the coboundary operator over F_2

Let $X$ be a pure $d$-dimensional weighted complex, and use the augmented convention $X(-1) = \{\emptyset\}$. For $-1 \le i \le d$, an **$i$-cochain** over $\mathbb{F}_2$ is a function $f : X(i) \to \mathbb{F}_2$; write $C^i = C^i(X; \mathbb{F}_2)$, so that $C^{-1} \cong \mathbb{F}_2$. For $-1 \le i < d$ the **coboundary operator** $\delta_i : C^i \to C^{i+1}$ is

$$
(\delta_i f)(\sigma) = \sum_{\tau \subset \sigma,\ |\tau| = |\sigma| - 1} f(\tau) \pmod 2.
$$

In particular $(\delta_{-1} c)(v) = c(\emptyset)$ for every vertex $v$, so $\delta_{-1}$ maps $C^{-1}$ onto the constant $0$-cochains. It satisfies $\delta_{i+1}\delta_i = 0$ for $-1 \le i \le d-2$. The **cocycles** are $Z^i = \ker \delta_i$, the **coboundaries** are $B^i = \operatorname{im} \delta_{i-1}$ for $0 \le i \le d$, and $H^i = Z^i / B^i$ is the $i$-th cohomology. Thus $B^0 = \{0, \mathbf{1}\}$ consists of the two constant $0$-cochains and $H^0$ is the reduced cohomology, which vanishes exactly when the $1$-skeleton of $X$ is connected. The **weighted norm** of an $i$-cochain, $0 \le i \le d$, is $\|f\| = \Pr_{\sigma \sim \Pi_i}[f(\sigma) \ne 0]$.

## Depends on

- [Pure weighted simplicial complexes and their face distributions](../local-spectral-high-dimensional-expanders/pure-weighted-complex.md)
- [Simplicial boundary matrix](../rational-homology-of-simplicial-complexes/boundary-matrix.md)

## Sources

- N. Linial, R. Meshulam, "Homological connectivity of random 2-complexes", Combinatorica 26 (2006) 475-487.
- M. Gromov, "Singularities, expanders and topology of maps. Part 2: from combinatorics to topology via algebraic isoperimetry", Geometric and Functional Analysis 20 (2010) 416-526.
- Y. Dikstein, I. Dinur, A. Lubotzky, "Low acceptance agreement tests via bounded-degree symplectic HDXs", FOCS (2024), arXiv:2402.01078, Section 2 (the augmented coboundary $\delta_{-1}$).
- T. Kaufman, D. Kazhdan, A. Lubotzky, "Ramanujan complexes and bounded degree topological expanders", FOCS (2014); Geometric and Functional Analysis 26 (2016), arXiv:1408.6351.
