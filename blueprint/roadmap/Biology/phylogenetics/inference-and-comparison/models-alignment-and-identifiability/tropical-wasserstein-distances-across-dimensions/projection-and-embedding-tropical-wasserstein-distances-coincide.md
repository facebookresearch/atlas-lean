# Projection and embedding tropical Wasserstein distances coincide

**Setting.** The max-plus *tropical semiring* is $\overline{\mathbb{R}}=\mathbb{R}\cup\{-\infty\}$ with $a\boxplus b=\max\{a,b\}$ and $a\odot b=a+b$. The *tropical projective torus* $\mathbb{R}^{n}/\mathbb{R}\mathbf{1}$ identifies $\mathbf{x}\sim\mathbf{x}+a\mathbf{1}$ and carries the *tropical metric*

$$d_{\mathrm{tr}}(\mathbf{x},\mathbf{y})=\max_i(x_i-y_i)-\min_i(x_i-y_i).$$

Spaces of phylogenetic trees with $N$ leaves embed in $\mathbb{R}^{N(N-1)/2}/\mathbb{R}\mathbf{1}$ as the vectors of pairwise leaf distances satisfying the four-point condition, so distributions of trees on *different* leaf sets live in tori of different dimensions. A tropical matrix $M\in\overline{\mathbb{R}}^{m\times n}$ (each row with a real entry) acts by $(M\mathbf{x})_i=\max_j(M_{ij}+x_j)$. For $n>m$, $M$ is a **simple projection** if each column has at most one real entry, so that $(M\mathbf{x})_i=\max_{j\in J_i}(M_{ij}+x_j)$ over disjoint non-empty index sets $J_i$. For probability measures $\mu$ on the $m$-torus and $\nu$ on the $n$-torus with finite $p$-th moments, let $W_{\mathrm{tr},p}$ be the $p$-Wasserstein distance for $d_{\mathrm{tr}}$ and define

$$W^-_{\mathrm{tr},p}(\mu,\nu)=\inf_{M}W_{\mathrm{tr},p}(\mu,M_\ast\nu),\qquad W^+_{\mathrm{tr},p}(\mu,\nu)=\inf\{W_{\mathrm{tr},p}(\alpha,\nu): M_\ast\alpha=\mu\},$$

infima over simple projections $M$ (projection versus embedding).

**Theorem.**

1. Every tropical matrix map is non-expansive: $d_{\mathrm{tr}}(M\mathbf{x},M\mathbf{y})\le d_{\mathrm{tr}}(\mathbf{x},\mathbf{y})$; hence $W_{\mathrm{tr},p}(M_\ast\alpha,M_\ast\nu)\le W_{\mathrm{tr},p}(\alpha,\nu)$, and push-forwards keep finite $p$-th moments.
2. $M$ is a simple projection if and only if every maximal cell of every fibre $M^{-1}(\mathbf{y})$ has dimension $n-m$.
3. **(Main result.)** For $p\in[1,\infty)$, $W^-_{\mathrm{tr},p}(\mu,\nu)=W^+_{\mathrm{tr},p}(\mu,\nu)<\infty$.
4. The common value $W^{m,n}_{\mathrm{tr},p}$ is $1$-Lipschitz in $(\mu,\nu)$ for $W_{\mathrm{tr},p}$, so its plug-in value on empirical measures of independent samples is a consistent estimator. It is not a metric: it vanishes whenever $\mu=M_\ast\nu$ for a simple projection $M$ (take $M$ in the infimum defining $W^-_{\mathrm{tr},p}$).

## Expansion

Non-expansiveness follows by comparing the maximizing indices in the rows realizing the tropical distance. The inequality $W^-\le W^+$ is immediate from non-expansiveness: if $M_\ast\alpha=\mu$ then $W(\mu,M_\ast\nu)\le W(\alpha,\nu)$. For the converse, a simple projection with equidimensional fibres admits a homeomorphism $f_M$ of the $n$-torus onto the product of the $m$-torus with the fibre over $\mathbf{0}$ whose inverse satisfies $d_{\mathrm{tr}}\bigl(f_M^{-1}(\mathbf{x},\mathbf{y}),f_M^{-1}(\mathbf{z},\mathbf{y})\bigr)=d_{\mathrm{tr}}(\mathbf{x},\mathbf{z})$ for a common fibre coordinate $\mathbf{y}$; given a near-optimal coupling of $\mu$ and $M_\ast\nu$, the gluing lemma lifts it to a coupling of $\nu$ with some $\alpha$ satisfying $M_\ast\alpha=\mu$ at no extra transport cost. This mirrors the Euclidean equivalence of projection and embedding Wasserstein distances under semi-orthogonal maps. For tree data, whether the optimal simple projection can be taken to map tree space into tree space is left open; the distance is computed in practice by optimizing over simple projections and applied to influenza tree samples.

## Sources

- Roan Talbut, Daniele Tramontano, Yueqi Cao, Mathias Drton and Anthea Monod, "Probability metrics for tropical spaces of different dimensions", Foundations of Data Science 10 (2026), 158–189, <https://doi.org/10.3934/fods.2026001>; numbering as in arXiv:2307.02846: Proposition 9, Lemma 16, Proposition 19, Corollary 21, Theorem 22, Remark 24, Proposition 25, Corollary 26, and Section 4.2 (phylogenetic tree spaces).
