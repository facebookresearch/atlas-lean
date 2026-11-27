# Airy limit law of the Sackin indices of random galled trees

**Setting.** A galled tree is a rooted phylogenetic network in which every reticulation cycle (gall) is vertex-disjoint from the others; simplex and normal galled trees are the subclasses studied alongside it. For a leaf $x$ of a galled tree $N$, let $h^+(x)$ and $h^-(x)$ be the lengths of a longest and a shortest path from the root to $x$. The two Sackin indices are

$$S^+(N) = \sum_{x \in L} h^+(x), \qquad S^-(N) = \sum_{x \in L} h^-(x),$$

summing over the leaf set $L$. Let $S_n^{(*,**)}$ be the Sackin index of a galled tree with $n$ leaves drawn uniformly from its class, labeled ($* = \ell$) or unlabeled ($* = u$), using longest ($** = \max$) or shortest ($** = \min$) paths.

**Theorem.** In every one of these cases, as $n \to \infty$,

$$\mathbb{E}\,S_n^{(*,**)} \sim \sqrt{\pi}\,\mu^{(*,**)}\,n^{3/2},$$

and, weakly and with convergence of all moments,

$$\frac{S_n^{(*,**)}}{\mu^{(*,**)}\,n^{3/2}} \xrightarrow{d} S,$$

where $S$ is the Airy distribution, determined by $\mathbb{E}S^m = \frac{2\sqrt{\pi}}{\Gamma((3m-1)/2)}\Omega_m$ for explicit constants $\Omega_m$ (so $\mathbb{E}S = \sqrt\pi$). The constants are:

| class | $\mu^{(\ell,\max)}$ | $\mu^{(\ell,\min)}$ | $\mu^{(u,\max)}$ | $\mu^{(u,\min)}$ |
|---|---|---|---|---|
| galled trees | $\frac{47}{32} + \frac{39\sqrt{17}}{544} \approx 1.76434$ | $\frac{49}{32} - \frac{7\sqrt{17}}{544} \approx 1.47820$ | $\approx 1.70991$ | $\approx 1.43507$ |
| simplex galled trees | $\sqrt{(2+\sqrt2)/2} \approx 1.30656$ | $\sqrt{(2+\sqrt2)/2} \approx 1.30656$ | $\approx 1.25148$ | $\approx 1.25148$ |
| normal galled trees | $\approx 0.64342$ | $\approx 0.60628$ | $\approx 1.12554$ | $\approx 1.06326$ |

## Proof sketch

As for phylogenetic trees, where the Sackin index of uniform trees also has an Airy limit, the counting generating functions of these galled-tree classes have a square-root singularity, and the Sackin index is an additive parameter whose bivariate generating function has a singular expansion that iterates to all moments; the Airy moments arise by singularity analysis. The constants decrease from general to simplex to normal galled trees because the number of galls decreases in that order, and replacing a gall by a tree shortens root-to-leaf paths. In simplex galled trees a root-to-leaf path passes through at most one gall, which explains why the longest-path and shortest-path constants coincide there.

## Sources

- Michael Fuchs and Bernhard Gittenberger, "Sackin indices for labeled and unlabeled classes of galled trees", *Journal of Mathematical Biology* 90 (2025), 42, <https://doi.org/10.1007/s00285-025-02205-0>. Preprint version: arXiv:2407.13892 (2024), definitions of $h^\pm$ and $S^\pm$, Theorems 1 and 2 with Tables 1 and 2 (Section 1), <https://doi.org/10.48550/arXiv.2407.13892>.
