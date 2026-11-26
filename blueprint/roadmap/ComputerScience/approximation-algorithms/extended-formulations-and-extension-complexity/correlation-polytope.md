# The correlation polytope

For $n \ge 1$, the **correlation polytope** $\mathrm{COR}(n) \subseteq \mathbb{R}^{n \times n}$ is the convex hull of the rank-one $0/1$ matrices $bb^\top$ for $b \in \{0,1\}^n$. For every $a \in \{0,1\}^n$ the inequality $\langle 2\,\mathrm{diag}(a) - aa^\top, x \rangle \le 1$ is valid, with slack $(1 - |a \cap b|)^2$ at the vertex $bb^\top$; the support of this slack matrix is the **non-unique-intersection** predicate $|a \cap b| \ne 1$.

## Depends on

- [Extended formulations and extension complexity](extended-formulation.md)

## Sources

- S. Fiorini, S. Massar, S. Pokutta, H. R. Tiwary and R. de Wolf, "Exponential Lower Bounds for Polytopes in Combinatorial Optimization", Journal of the ACM 62(2), 2015.
- V. Kaibel and S. Weltge, "A Short Proof that the Extension Complexity of the Correlation Polytope Grows Exponentially", Discrete & Computational Geometry 53(2), 2015.
