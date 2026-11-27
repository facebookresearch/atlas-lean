# Confidence sets for the Fréchet mean phylogenetic tree in BHV space

Let $\mathcal T_m$ be Billera–Holmes–Vogtmann (BHV) space of metric phylogenetic trees, a CAT(0) space made of Euclidean orthants, one per tree topology, with geodesic distance $d$. For a distribution $F$ on $\mathcal T_m$, the **Fréchet function** is $G(u) = \int d(q,u)^2\, F(dq)$ and the **Fréchet mean** is $T^* = \arg\min_u G(u)$. For a tree $T$ in a top-dimensional orthant, let $\Phi_T : \mathcal T_m \to \mathbb R^m$ be the log map: it sends each tree to the Euclidean vector of the initial direction and length of its geodesic from $T$.

**Theorem (central limit theorem).** Let $T_1,\dots,T_n$ be i.i.d. from $F$ with finite Fréchet function. Suppose the Fréchet mean $T^*$ lies in a top-dimensional stratum and $F(D_{T^*}) = 0$, where $D_{T^*}$ is the set of trees on the boundaries of the maximal cells of $T^*$. Then the sample Fréchet mean $\hat T_n$ satisfies

$$
\sqrt n\,\big(\Phi_{\hat T_n}(\hat T_n) - \Phi_{T^*}(T^*)\big) \xrightarrow{\mathcal D} \mathcal N(0, \Sigma)
$$

for a covariance matrix $\Sigma$ determined by $F$.

**Proposition (consistency of the estimated log map).** If $T^*$ is not on an orthant boundary and $\int d(\mathbf 0, T)^2\, dF(T) < \infty$, where $\mathbf 0$ is the star tree, then for every fixed $t$, $\Phi_{\hat T_n}(t) \to \Phi_{T^*}(t)$ almost surely as $n \to \infty$.

**Confidence set.** With $\bar\Phi = \frac1n\sum_i \Phi_{\hat T_n}(T_i)$ and sample covariance $S$, the set

$$
A = \Big\{ T_0 \in \mathcal T_m : \big(\bar\Phi - \Phi_{\hat T_n}(T_0)\big)^\top S^{-1}\big(\bar\Phi - \Phi_{\hat T_n}(T_0)\big) < \frac{m(n-1)}{n(n-m)}\, F_{m, n-m}(1 - \alpha) \Big\}
$$

is an asymptotic $100(1-\alpha)\%$ confidence set for $T^*$. It may contain trees of several topologies near the mean.

## Depends on

- [The space of phylogenetic trees is CAT(0)](../../../not-yet-classified/phylogenetic-tree-space/tree-space-is-cat0.md)

## Expansion

Away from orthant boundaries, BHV space is locally Euclidean around $T^*$. The log map linearizes a neighborhood of the mean, and the Fréchet mean's first-order condition becomes $\mathbb E\,\Phi_{T^*}(T) = \Phi_{T^*}(T^*)$. The CLT of Barden, Le and Owen accounts for estimating both $T^*$ and the chart $\Phi_{T^*}$. Combining it with Hotelling's $T^2$ pivot gives the Euclidean-looking ellipsoid, which is pulled back to tree space through the estimated log map. The sample mean is computed with Bačák's proximal-point algorithm. Coverage is accurate when the projected sample is close to multivariate normal; the method breaks down when the mean sits on a boundary, where stickiness occurs.

## Sources

- Amy Willis, "Confidence Sets for Phylogenetic Trees", Journal of the American Statistical Association 114 (2019), 235–244, <https://doi.org/10.1080/01621459.2017.1395342>. Published version of arXiv:1607.08288, cited next; locators there refer to the arXiv version.
- Amy Willis, "Confidence sets for phylogenetic trees", arXiv (2016). Theorem 1 (due to Barden, Le and Owen), Proposition 1, Section 4 (procedure). <https://doi.org/10.48550/arXiv.1607.08288>
