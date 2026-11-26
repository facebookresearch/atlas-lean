# Every f-divergence induces the Fisher information metric on tree space

Fix a fully resolved topology on $N$ leaves with edge lengths $\ell \in \mathbb{R}_{>0}^{2N-3}$, and let $p_\ell(s)$, $s \in \{0, 1\}^N$, be the distribution of leaf characters under the [two-state symmetric process](leaf-covariances-of-the-two-state-symmetric-process.md). The Fisher information metric is

$$g_{ij}(\ell) = \sum_{s \in \{0,1\}^N} p_\ell(s)\, \partial_i \log p_\ell(s)\, \partial_j \log p_\ell(s).$$

For a convex $f$ with $f(1) = 0$, the $f$-divergence is $D_f(p; q) = \sum_s q(s) f\bigl(p(s)/q(s)\bigr)$. If $f$ is twice differentiable at $1$ with $f''(1) > 0$, then as the perturbation $\delta$ of the edge lengths tends to $0$

$$\sum_{i,j} \delta_i\, g_{ij}(\ell)\, \delta_j = \frac{2}{f''(1)}\, D_f\bigl(p_{\ell+\delta}; p_\ell\bigr) + o(|\delta|^2).$$

If moreover $f$ is three times continuously differentiable near $1$, the remainder is $O(|\delta|^3)$, as in Lemma 3.1 of the source. Without that extra smoothness a cubic remainder can fail: $f(1+x) = x^2 + |x|^{5/2}$ is convex with $f(1) = 0$ and $f''(1) = 2$, yet contributes a term of order $|\delta|^{5/2}$ in every direction that changes the distribution.

Let $\mathcal W_N$ be [wald space](leaf-covariances-of-the-two-state-symmetric-process.md), the quotient of the forests on $N$ labelled leaves by its BHV and boundary-at-infinity rules, which the map $[F] \mapsto p_F$ embeds in the distributions on $\{0,1\}^N$. Suppose in addition (Theorem 3.1 of the source) that $d$ and $d'$ are square roots of an $f$- and an $f'$-divergence and are themselves **metrics** on the distributions of characters, as the Hellinger and Jensen–Shannon metrics are; the square root of the Kullback–Leibler divergence is not, since it is not even symmetric. Then the intrinsic (path-length) metrics $d^*$ and $d'^*$ that they induce on $\mathcal W_N$ are finite and satisfy $d^* = c\, d'^*$ for a constant $c > 0$, and distance-realizing paths solve the geodesic equation of $g$ inside each maximal orthant.

## Depends on

- [Leaf covariances of the two-state symmetric process on a tree](leaf-covariances-of-the-two-state-symmetric-process.md)

## Expansion

Since $p_\ell(s) > 0$ for finite edge lengths, the Peano form of Taylor's theorem for $f$ at $1$ gives $D_f(p_{\ell+\delta}; p_\ell) = \tfrac{f''(1)}{2} \sum_s (p_{\ell+\delta}(s) - p_\ell(s))^2 / p_\ell(s) + o(|\delta|^2)$ (with $O(|\delta|^3)$ when $f$ is $C^3$ near $1$), and the first-order expansion $p_{\ell+\delta} - p_\ell = \sum_i \delta_i \partial_i p_\ell + O(|\delta|^2)$ turns the chi-square sum into the Fisher quadratic form (the first-order term vanishes since $\sum_s f'(1)(p_{\ell+\delta}(s) - p_\ell(s)) = 0$). The Kullback–Leibler divergence ($f(t) = t \log t$), squared Hellinger and squared Jensen–Shannon metrics all satisfy the local expansion, so the local geometry does not depend on the divergence chosen; the global comparison uses only divergences whose square roots are metrics. Positive definiteness of $g$ follows because distinct trees give distinct character distributions.

## Sources

- M. K. Garba et al., *Information geometry for phylogenetic trees*, J. Math. Biol. 82 (2021), 19. <https://doi.org/10.1007/s00285-021-01553-x> (PMCID: PMC7884381) Section 3, Equations (3.1) and (3.3), Lemma 3.1 and Theorem 3.1.
