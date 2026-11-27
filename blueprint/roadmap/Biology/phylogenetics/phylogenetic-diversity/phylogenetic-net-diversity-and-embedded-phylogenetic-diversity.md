# Phylogenetic net diversity and embedded phylogenetic diversity on networks

Let $\mathcal N$ be a rooted phylogenetic network on a taxon set $X$ with root $\rho$ and nonnegative edge lengths $\lambda_e$. Each reticulation $r$ with parents $p_1,p_2$ carries *inheritance probabilities* $\gamma_{(p_1,r)}\in(0,1)$ and $\gamma_{(p_2,r)}=1-\gamma_{(p_1,r)}$ (default $\tfrac12$); every tree edge has probability $1$, and the probability $\mathbb P(P)$ of a directed path is the product of its edge probabilities. $\mathsf T(\mathcal N)$ is the multiset of rooted phylogenetic $X$-trees *displayed* by $\mathcal N$, obtained by deleting one incoming edge at each reticulation and suppressing indegree-1 outdegree-1 vertices; with $k$ reticulations, $|\mathsf T(\mathcal N)|\le 2^k$.

**Phylogenetic diversity on trees.** For a rooted tree $\mathcal T$ and $S\subseteq X$, $PD_{\mathcal T}(S)$ is the total edge length of the smallest subtree containing $S$ and the root.

**Network generalizations.** For $S\subseteq X$:

- *Phylogenetic net diversity* $PND(S)$: the total length of a minimum-cost arborescence of $\mathcal N$ containing $\rho$ and $S$ (variants: $PND^{ML}$ uses a most probable such arborescence, $PND^{inh}$ averages over them by probability).
- *Phylogenetic subnet diversity* $PSD(S)$: the total length of the subnetwork $\mathcal N_S$ of all vertices and edges on some root-to-$S$ path.
- *Embedded phylogenetic diversity*: $PD^{\min}_{\mathsf T(\mathcal N)}(S)=\min_{\mathcal T\in\mathsf T(\mathcal N)}PD_{\mathcal T}(S)$, and similarly $PD^{\max}$, $PD^{\Sigma}$ (sum) and $PD^{\varnothing}$ (mean over $\mathsf T(\mathcal N)$), plus the probability-weighted mean $PD^{\varnothing_{inh}}$ and the value $PD^{ML}$ on a most probable displayed tree.
- *LSA associated diversity* $PD^{LSA}(S)$: $PD$ computed on the lowest-stable-ancestor tree of $\mathcal N$.

**Proposition.** Let $\mathcal N$ be binary with $k$ reticulations. Then for all $S\subseteq X$,

$$PND(S) \le PD^{\min}_{\mathsf T(\mathcal N)}(S),$$

with equality for all $S$ whenever $|\mathsf T(\mathcal N)|=2^k$, i.e. whenever every choice of one incoming edge per reticulation yields a phylogenetic $X$-tree (for example, for normal networks).

## Depends on

- [Greedy maximization of phylogenetic diversity](greedy-maximization-of-phylogenetic-diversity.md)

## Expansion

Every displayed tree, before suppression of degree-2 vertices, is a spanning arborescence of $\mathcal N$, and restricting it to the root-to-$S$ paths gives an arborescence containing $\rho$ and $S$ with length $PD_{\mathcal T}(S)$; hence $PND(S)$, a minimum over a larger family, is at most the minimum over displayed trees. Conversely, a minimum-cost arborescence for $S$ selects at most one incoming edge at each reticulation it uses, and extending that selection arbitrarily at the other reticulations gives a choice of one edge per reticulation; when all $2^k$ choices produce displayed trees, this tree has $PD_{\mathcal T}(S)=PND(S)$. In the worked example of the source, $S=\{A,B\}$ has $PND=4$ but $PND^{ML}=5$, showing that the most probable arborescence need not be the cheapest.

## Sources

- Kristina Wicke, Mareike Fischer, "Phylogenetic diversity and biodiversity indices on phylogenetic networks", Mathematical Biosciences 298 (2018), 80–90, <https://doi.org/10.1016/j.mbs.2018.02.005>. Published version of arXiv:1706.05279, cited next; locators there refer to the arXiv version.
- Kristina Wicke and Mareike Fischer, "Phylogenetic diversity and biodiversity indices on phylogenetic networks", arXiv:1706.05279 (2017), Section 2 (inheritance probabilities, Definitions 1-4, Theorem 1), Section 3 (Definitions 5-8, Proposition 1), Section 4 (Definitions 9-12 and the remarks after Definition 12), <https://doi.org/10.48550/arXiv.1706.05279>. Published in Mathematical Biosciences (2018).
