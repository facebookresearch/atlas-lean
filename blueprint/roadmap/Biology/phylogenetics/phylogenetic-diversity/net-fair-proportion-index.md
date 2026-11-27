# Net Fair Proportion Index on phylogenetic networks

Let $\mathcal N$ be a rooted phylogenetic network on a taxon set $X$ with root $\rho$ and nonnegative edge lengths $\lambda_e$. Each reticulation $r$ with parents $p_1,p_2$ carries *inheritance probabilities* $\gamma_{(p_1,r)}\in(0,1)$ and $\gamma_{(p_2,r)}=1-\gamma_{(p_1,r)}$ (default $\tfrac12$); every tree edge has probability $1$, and the probability $\mathbb P(P)$ of a directed path is the product of its edge probabilities. $\mathsf T(\mathcal N)$ is the multiset of rooted phylogenetic $X$-trees *displayed* by $\mathcal N$, obtained by deleting one incoming edge at each reticulation and suppressing indegree-1 outdegree-1 vertices; with $k$ reticulations, $|\mathsf T(\mathcal N)|\le 2^k$.

**On trees.** For a rooted tree $\mathcal T$, the Fair Proportion Index of a taxon $a$ is $FP_{\mathcal T}(a)=\sum_e\lambda_e/D_e$, summed over the edges $e$ on the path from the root to $a$, where $D_e$ is the number of leaves below $e$. It coincides with the Shapley value of the cooperative game $S\mapsto PD_{\mathcal T}(S)$:

$$SV_{\mathcal T}(a) = \frac{1}{n!}\sum_{a\in S\subseteq X}(|S|-1)!\,(n-|S|)!\,\big(PD_{\mathcal T}(S)-PD_{\mathcal T}(S\setminus\{a\})\big) = FP_{\mathcal T}(a), \qquad n=|X|.$$

**Definition.** For an edge $e$ of $\mathcal N$ and a leaf $d$ below it, let $\mathbb P^e_{desc}(d)=\sum_{P}\mathbb P(P)$, summed over the directed paths $P$ from the head of $e$ to $d$. The *Net Fair Proportion Index* of $a\in X$ is

$$NFP(a) = \sum_{P\in\mathcal P_{\rho a}}\mathbb P(P)\sum_{e\in P}\frac{\lambda_e}{\sum_{d\in D_e}\mathbb P^e_{desc}(d)},$$

where $\mathcal P_{\rho a}$ is the set of root-to-$a$ paths and $D_e$ the set of leaves below $e$.

**Properties.**

1. *Efficiency:* $\sum_{a\in X}NFP(a)=\sum_e \mathbb P(e)\,\lambda_e$, which is the total edge length of $\mathcal N$ when, as in the source's examples, reticulation (hybridization) edges have length $0$; the source states efficiency in this form, $\sum_a NFP(a)=\mathrm{weight}(\mathcal N)$.
2. *Tree reduction:* if $\mathcal N$ is a tree, $NFP(a)=FP(a)$ for all $a$.

**Other indices.** Embedded versions $FP^{\ast}_{\mathsf T(\mathcal N)}$ and $SV^{\ast}_{\mathsf T(\mathcal N)}$ ($\ast\in\{\min,\max,\Sigma,\varnothing,\varnothing_{inh},ML\}$) aggregate the tree indices over displayed trees, and a generalized Shapley value replaces $PD$ by any of the network diversity measures ($PND$, $PSD$, embedded or LSA diversity).

## Depends on

- [Phylogenetic net diversity and embedded phylogenetic diversity on networks](phylogenetic-net-diversity-and-embedded-phylogenetic-diversity.md)

## Expansion

The index distributes the length of each edge $e$ among the leaves below it in proportion to the probability that a leaf descends through $e$, and then weights each root-to-$a$ path by its inheritance probability. Summing over all taxa, the root-to-leaf paths through a fixed edge $e=(u,v)$ carry total weight $\big(\sum_{P:\rho\to u}\mathbb P(P)\big)\,\mathbb P(e)\sum_{d\in D_e}\mathbb P^e_{desc}(d)$. The first factor is $1$ for every vertex (by induction, since incoming probabilities at each vertex sum to $1$), and the last factor cancels the denominator, so $e$ hands out exactly $\mathbb P(e)\lambda_e$; tree edges have $\mathbb P(e)=1$. On a tree every path probability is $1$ and $\mathbb P^e_{desc}(d)=1$ for all leaves below $e$, so the denominator is $D_e$ and the definition reduces to the Fair Proportion Index. The tree identity $FP=SV$ does not automatically carry over to networks, which is why the source defines both families and studies them separately.

## Sources

- Kristina Wicke, Mareike Fischer, "Phylogenetic diversity and biodiversity indices on phylogenetic networks", Mathematical Biosciences 298 (2018), 80–90, <https://doi.org/10.1016/j.mbs.2018.02.005>. Published version of arXiv:1706.05279, cited next; locators there refer to the arXiv version.
- Kristina Wicke and Mareike Fischer, "Phylogenetic diversity and biodiversity indices on phylogenetic networks", arXiv:1706.05279 (2017), Section 2 (inheritance probabilities, Definitions 1-4, Theorem 1), Section 3 (Definitions 5-8, Proposition 1), Section 4 (Definitions 9-12 and the remarks after Definition 12), <https://doi.org/10.48550/arXiv.1706.05279>. Published in Mathematical Biosciences (2018).
