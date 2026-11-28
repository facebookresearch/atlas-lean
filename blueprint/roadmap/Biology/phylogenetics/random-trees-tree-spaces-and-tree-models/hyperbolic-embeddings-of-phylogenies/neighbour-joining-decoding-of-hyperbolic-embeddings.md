# Neighbour-joining decoding of hyperbolic embeddings

**Setting.** For curvature $\kappa < 0$ and dimension $d \ge 2$, the hyperboloid model is $\mathbb H^d = \{x \in \mathbb R^{d+1} : \langle x, x\rangle = -1, x_0 > 0\}$ with Lorentz product $\langle x, y\rangle = -x_0y_0 + \sum_{i \ge 1}x_iy_i$ and distance

$$d_\kappa(x, y) = \frac{1}{\sqrt{-\kappa}}\operatorname{arcosh}\big(-\langle x, y\rangle\big).$$

Taxa $1, \dots, n$ are represented by points $X = (x_1, \dots, x_n)$, parametrized by their tangent coordinates $(x_1, \dots, x_d) \mapsto (\sqrt{1 + \|x\|^2}, x)$, and a tree is decoded as $T = \mathrm{NJ}(D(X))$ with $D_{ij} = d_\kappa(x_i, x_j)$. A metric space is **$\delta$-hyperbolic** if every quadruple satisfies the relaxed four-point condition

$$d(x,w) + d(y,z) \le \max\{d(x,y) + d(z,w),\, d(x,z) + d(y,w)\} + 2\delta;$$

$\delta = 0$ is exactly the condition for $D$ to be additive (realized by a weighted tree).

**Theorem.**
1. For every $d \ge 2$ and $\kappa < 0$, $\mathbb H^d$ with curvature $\kappa$ is $\delta$-hyperbolic, and the minimal constant scales as $\delta_{d,\kappa} = \delta_{d,-1}/\sqrt{-\kappa}$; in particular $\delta_{d,\kappa} \to 0$ as $\kappa \to -\infty$.
2. (Stability of neighbour-joining) If $\|D - D_T\|_\infty < \tfrac12 \min_{e \in E(T)} \ell_e$ for an additive tree metric $D_T$, then $\mathrm{NJ}(D)$ has the topology of $T$.

## Depends on

- [Atteson's theorem: neighbor joining has sup-norm radius one half](../../atteson-s-theorem-on-neighbor-joining/nj-run-splits-of-abs-sub-lt.md)

## Expansion

Part 1: all hyperbolic spaces of constant curvature $\kappa$ are rescalings of the unit-curvature space by the factor $1/\sqrt{-\kappa}$, and the four-point defect scales linearly with distances, which gives the scaling of $\delta$. Part 2 is the $\ell_\infty$ radius $1/2$ of neighbour-joining. The source combines the two heuristically: for strongly negative curvature the four-point defect is small, so NJ should be in its consistent regime, and since hyperbolic distances are continuous in $X$ the decoded branch lengths would be too, which motivates Markov chain Monte Carlo that moves taxon points in $\mathbb R^{n \times d}$ instead of making discrete tree moves. This is not a theorem for a fixed embedding: for fixed $X$, $D(X)$ is only rescaled by $1/\sqrt{-\kappa}$ as $\kappa$ varies, and neighbour-joining is scale invariant, so changing $\kappa$ resolves no tie (four points with tangent coordinates of equal norm at angles $0, \pi/2, \pi, 3\pi/2$ leave the two quartet splits $12|34$ and $14|23$ tied for every $\kappa < 0$); the defect is small relative to the branch lengths only if the embedding is rescaled with $\kappa$.

## Sources

- M. Macaulay, A. Darling, M. Fourment, "Fidelity of hyperbolic space for Bayesian phylogenetic inference", PLoS Computational Biology 19(4) (2023) e1011084, Eqs. (1)–(2), Theorems 1–2, Corollary 3 and Algorithm 1, <https://doi.org/10.1371/journal.pcbi.1011084>, PMCID PMC10166537.
