# Every f-divergence induces the Fisher information metric on tree space

Fix a fully resolved topology on $N$ leaves with edge lengths $\ell \in \mathbb{R}_{>0}^{2N-3}$, and let $p_\ell(s)$, $s \in \{0, 1\}^N$, be the distribution of leaf characters under the [two-state symmetric process](leaf-covariances-of-the-two-state-symmetric-process.md). The Fisher information metric is

$$g_{ij}(\ell) = \sum_{s \in \{0,1\}^N} p_\ell(s)\, \partial_i \log p_\ell(s)\, \partial_j \log p_\ell(s).$$

For a convex $f$ with $f(1) = 0$, the $f$-divergence is $D_f(p; q) = \sum_s q(s) f\bigl(p(s)/q(s)\bigr)$. If $f$ is twice differentiable at $1$ with $f''(1) > 0$, then for a small perturbation $\delta$ of the edge lengths

$$\sum_{i,j} \delta_i\, g_{ij}(\ell)\, \delta_j = \frac{2}{f''(1)}\, D_f\bigl(p_{\ell+\delta}; p_\ell\bigr) + O(|\delta|^3).$$

Consequently, if $d$ and $d'$ are the square roots of two such $f$-divergences on distributions of characters, the intrinsic (path-length) metrics $d^*$ and $d'^*$ they induce on wald space are finite and satisfy $d^* = c\, d'^*$ for a constant $c > 0$; distance-realizing paths solve the geodesic equation of $g$ inside each maximal orthant.

## Depends on

- [Leaf covariances of the two-state symmetric process on a tree](leaf-covariances-of-the-two-state-symmetric-process.md)

## Expansion

Taylor expansion of $f$ at $1$ gives $D_f(p_{\ell+\delta}; p_\ell) = \tfrac{f''(1)}{2} \sum_s (p_{\ell+\delta}(s) - p_\ell(s))^2 / p_\ell(s) + O(|\delta|^3)$, and the first-order expansion $p_{\ell+\delta} - p_\ell = \sum_i \delta_i \partial_i p_\ell + O(|\delta|^2)$ turns the chi-square sum into the Fisher quadratic form (the first-order term vanishes since $\sum_s f'(1)(p_{\ell+\delta}(s) - p_\ell(s)) = 0$). The Kullback–Leibler divergence ($f(t) = t \log t$), squared Hellinger and squared Jensen–Shannon metrics all qualify, so the geometry does not depend on the divergence chosen. Positive definiteness of $g$ follows because distinct trees give distinct character distributions.

## Sources

- M. K. Garba et al., *Information geometry for phylogenetic trees*, J. Math. Biol. 82 (2021), 19. <https://doi.org/10.1007/s00285-021-01553-x> (PMCID: PMC7884381) Section 3, Equations (3.1) and (3.3), Lemma 3.1 and Theorem 3.1.
