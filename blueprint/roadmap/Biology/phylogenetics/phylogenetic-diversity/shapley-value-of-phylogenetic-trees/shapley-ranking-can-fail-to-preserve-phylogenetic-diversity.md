# Shapley-value ranking can fail to preserve phylogenetic diversity

Let $\mathcal{T}$ be an unrooted binary phylogenetic tree with positive edge lengths, $PD(S)$ the length of the subtree spanning a set of leaves $S$, and $SV_i$ the Shapley value of leaf $i$ in the phylogenetic tree game $(X, PD)$. The **Noah's ark problem** in its simplest form asks for $k$ species maximizing $PD$; the maximum $pd_k = \max\{ PD(W) : |W| = k \}$ is attained by a greedy algorithm. Ranking species by $SV_i$ and keeping the top $k$ is not a constant-factor approximation of $pd_k$, or even of $PD(X)$.

**Theorem.** Let $k \ge 1$ and let $\mathcal{T}_\varepsilon$ have $n = 2k+1$ leaves, consisting of a rooted subtree $\mathcal{T}_1$ with $k$ leaves and a rooted subtree $\mathcal{T}_2$ with $k+1$ leaves joined by an edge of length $1/\varepsilon$, where all $2k-2$ edges of $\mathcal{T}_1$ have length $\frac{\varepsilon}{2k-2}$ and all $2k$ edges of $\mathcal{T}_2$ have length $\frac{\varepsilon}{2k}$. If

$$ 0 < \varepsilon < \sqrt{\frac{k+2}{k^3 + 3k^2 - 2}}, $$

then for every $k' \le k$ the $k'$ species of largest Shapley value all lie in $\mathcal{T}_1$. Hence their diversity is at most $PD(\mathcal{T}_1) = \varepsilon \to 0$ as $\varepsilon \to 0$, while $PD(X) = 2\varepsilon + 1/\varepsilon \to \infty$ and already two species, one from each side, reach diversity at least $1/\varepsilon$.

## Depends on

- [Greedy maximization of phylogenetic diversity](../greedy-maximization-of-phylogenetic-diversity.md)
- [Shapley transformation of an unrooted phylogenetic tree and its failure to determine topology](shapley-transformation-of-unrooted-trees-does-not-determine-topology.md)

## Expansion

By the split-count formula, the long central edge contributes $\frac{k+1}{(2k+1)k} \cdot \frac{1}{\varepsilon}$ to the Shapley value of each leaf of the smaller side $\mathcal{T}_1$, but only $\frac{k}{(2k+1)(k+1)} \cdot \frac{1}{\varepsilon}$ to each leaf of $\mathcal{T}_2$: leaves on the smaller side receive a larger share of the edge separating them from the majority. Bounding the contributions of the short edges by their split factors and lengths gives $\min_{\mathcal{T}_1} SV > \max_{\mathcal{T}_2} SV$ whenever $\varepsilon^2 < \frac{k+2}{k^3 + 3k^2 - 2}$. The top-ranked species therefore cluster on one side of the long edge and miss it entirely, whereas the greedy algorithm starts from a pair of maximally distant leaves and always includes it.

## Sources

- Kristina Wicke, Mareike Fischer, "On the Shapley Value of Unrooted Phylogenetic Trees", Bulletin of Mathematical Biology 81 (2019), 618–638, <https://doi.org/10.1007/s11538-018-0392-8>. Published version of arXiv:1707.09908, cited next; locators there refer to the arXiv version.
- Kristina Wicke, Mareike Fischer, "On the Shapley value of unrooted phylogenetic trees", arXiv (2017). Section 4 (the Shapley value and the Noah's ark problem, theorem on the trees $\mathcal{T}_\varepsilon$). <https://doi.org/10.48550/arXiv.1707.09908>
