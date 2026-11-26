# Neighbour-joining decoding of hyperbolic embeddings

**Setting.** For curvature $\kappa < 0$ and dimension $d \ge 2$, the hyperboloid model is $\mathbb H^d = \{x \in \mathbb R^{d+1} : \langle x, x\rangle = -1, x_0 > 0\}$ with Lorentz product $\langle x, y\rangle = -x_0y_0 + \sum_{i \ge 1}x_iy_i$ and distance
$$d_\kappa(x, y) = \frac{1}{\sqrt{-\kappa}}\operatorname{arcosh}\big(-\langle x, y\rangle\big).$$
Taxa $1, \dots, n$ are represented by points $X = (x_1, \dots, x_n)$, parametrized by their tangent coordinates $(x_1, \dots, x_d) \mapsto (\sqrt{1 + \|x\|^2}, x)$, and a tree is decoded as $T = \mathrm{NJ}(D(X))$ with $D_{ij} = d_\kappa(x_i, x_j)$. A metric space is **$\delta$-hyperbolic** if every quadruple satisfies the relaxed four-point condition
$$d(x,w) + d(y,z) \le \max\{d(x,y) + d(z,w),\, d(x,z) + d(y,w)\} + 2\delta;$$
$\delta = 0$ is exactly the condition for $D$ to be additive (realized by a weighted tree).

**Theorem.**
1. For every $d \ge 2$ and $\kappa < 0$, $\mathbb H^d$ with curvature $\kappa$ is $\delta$-hyperbolic, and the minimal constant scales as $\delta_{d,\kappa} = \delta_{d,-1}/\sqrt{-\kappa}$; in particular $\delta_{d,\kappa} \to 0$ as $\kappa \to -\infty$.
2. (Stability of neighbour-joining) If $\|D - D_T\|_\infty < \tfrac12 \min_{e \in E(T)} \ell_e$ for an additive tree metric $D_T$, then $\mathrm{NJ}(D)$ has the topology of $T$.
3. Consequently, as $\kappa \to -\infty$, the embedded distances approach tree-additive distances, neighbour-joining decodes a unique tree, and the length of the decoded tree $\ell(\mathrm{NJ}(D(X)))$ depends continuously on the embedding locations $X$, even across topology changes.

## Depends on

- [Atteson's theorem on neighbor-joining](../atteson-s-theorem-on-neighbor-joining/README.md)

## Expansion

Part 1: all hyperbolic spaces of constant curvature $\kappa$ are rescalings of the unit-curvature space by the factor $1/\sqrt{-\kappa}$, and the four-point defect scales linearly with distances, which gives the scaling of $\delta$. Part 2 is the $\ell_\infty$ radius $1/2$ of neighbour-joining. Part 3 combines the two: for sufficiently negative curvature the defect of the embedded distances is small relative to the shortest branch, so NJ is in its consistent regime, where its output distances match the input distances up to the defect; since hyperbolic distances are continuous in $X$, so are the decoded branch lengths and total tree length. This continuity justifies Markov chain Monte Carlo that moves taxon points in $\mathbb R^{n \times d}$ instead of making discrete tree moves. When the curvature is too close to $0$, NJ ties and non-additivity make the decoded tree depend on arbitrary merge choices, and the embedding loses fidelity for Bayesian inference.

## Sources

- M. Macaulay, A. Darling, M. Fourment, "Fidelity of hyperbolic space for Bayesian phylogenetic inference", PLoS Computational Biology 19(4) (2023) e1011084, Eqs. (1)–(2), Theorems 1–2, Corollary 3 and Algorithm 1, <https://doi.org/10.1371/journal.pcbi.1011084>, PMCID PMC10166537.
