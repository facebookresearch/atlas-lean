# Coboundary expansion of a simplicial complex

Let $X$ be a pure weighted complex and $0 \le i < d$. The **$i$-th coboundary expansion** of $X$ over $\mathbb{F}_2$ is

$$
h^i(X) = \min_{f \in C^i \setminus B^i} \frac{\|\delta_i f\|}{\operatorname{dist}(f, B^i)}, \qquad \operatorname{dist}(f, B^i) = \min_{g \in B^i} \|f - g\|.
$$

$X$ is an **$\varepsilon$-coboundary expander** in dimension $i$ if $h^i(X) \ge \varepsilon$. A positive $h^i(X)$ forces $H^i(X; \mathbb{F}_2) = 0$. For $i = 0$ and $X$ a graph, $h^0$ is the normalized edge expansion (Cheeger constant) of the $1$-skeleton.

## Depends on

- [Cochains and the coboundary operator over F_2](cochains-coboundary.md)

## Sources

- N. Linial, R. Meshulam, "Homological connectivity of random 2-complexes", Combinatorica 26 (2006) 475-487.
- M. Gromov, "Singularities, expanders and topology of maps. Part 2: from combinatorics to topology via algebraic isoperimetry", Geometric and Functional Analysis 20 (2010) 416-526.
- A. Lubotzky, "High dimensional expanders", Proceedings of the ICM (2018), arXiv:1712.02526.
