# MaxWeightTree-PD and MinWeightTree-PD on phylogenetic networks

Let $\mathcal{N}$ be a rooted binary phylogenetic network on taxa $X$ with nonnegative arc weights $w$. For $S \subseteq X$:

- **AllPaths-PD** $_{\mathcal{N}}(S) = \sum_{e \in \mathrm{Anc}(S)} w(e)$, summing over arcs on some root-to-$S$ path;
- **Network-PD** $_{\mathcal{N},p}(S) = \sum_e \gamma(S,e)\,w(e)$, where an inheritance proportion $p(e) \in [0,1]$ sits on each reticulation arc and $\gamma(S,\cdot)$ is computed bottom-up: $\gamma(S,e) = 1_{v \in S}$ for a pendant arc into leaf $v$, $\gamma(S,e) = \gamma(S,f_1) + \gamma(S,f_2) - \gamma(S,f_1)\gamma(S,f_2)$ above a tree vertex with child arcs $f_1, f_2$, and $\gamma(S,e) = p(e)\,\gamma(S,f)$ for an arc $e$ into a reticulation with child arc $f$;
- **MaxWeightTree-PD** and **MinWeightTree-PD** $_{\mathcal{N}}(S)$: the maximum and minimum total weight of a connecting subtree (root-rooted arborescence in $\mathcal{N}$ with leaf set $S$).

The optimization problems ask for the maximum score over all $S \subseteq X$ with $|S| = k$.

**Theorem 5.3 (Network-PD envelope).** Let $P$ be the set of inheritance proportions with $p(e_1) + p(e_2) = 1$ at each reticulation with incoming arcs $e_1, e_2$. For every $S \subseteq X$,

$$\max_{p\in P}\mathrm{Network\text{-}PD}_{\mathcal{N},p}(S) = \mathrm{MaxWeightTree\text{-}PD}_{\mathcal{N}}(S), \qquad \min_{p\in P}\mathrm{Network\text{-}PD}_{\mathcal{N},p}(S) = \mathrm{MinWeightTree\text{-}PD}_{\mathcal{N}}(S),$$

and (Corollary 5.4) the same identities hold for the $k$-subset maximization problems.

**Theorem 6.1.** Max-MaxWeightTree-PD is solvable in polynomial time on every phylogenetic network.

**Theorems 7.1–7.4.** Computing a minimum-weight connecting tree for all of $X$ is NP-hard in general (7.1) but polynomial on tree-child networks (7.2); computing MinWeightTree-PD$_{\mathcal{N}}(S)$ for a given strict subset $S$ is NP-hard even on normal networks (7.3); and Max-MinWeightTree-PD is NP-hard (7.4).

When features at a reticulation are replaced rather than added, true Network-PD lies between the two tree scores; the optimistic bound is easy to optimize, the pessimistic one is not.

## Depends on

- [Hardness and greedy approximation of AllPaths-PD and Network-PD](hardness-and-greedy-approximation-of-allpaths-and-network-pd.md)

## Expansion

Network-PD is linear in each reticulation's proportion pair once the others are fixed, so its extremes over $P$ occur at $0/1$ choices, which select exactly one incoming arc per reticulation, i.e. a connecting tree. Maximizing tree weight over $k$-subsets reduces to a maximum-weight flow: send $k$ units from the root through arcs of capacity $1$ (plus auxiliary root arcs of capacity $k$) to a sink attached to the leaves, with arc weights as profits; integral optimal flows give the optimal tree. The minimum-weight hardness comes from Exact Cover by 3-Sets: set vertices with weight-3 root arcs feeding element leaves force a minimum connecting tree to choose an exact cover. On tree-child networks every connecting tree for $X$ contains all tree arcs and one incoming arc per reticulation, so picking the lighter incoming arc independently is optimal.

## Sources

- Magnus Bordewich, Charles Semple and Kristina Wicke, "On the complexity of optimising variants of phylogenetic diversity on phylogenetic networks", Theoretical Computer Science 917 (2022), 66–80, <https://doi.org/10.1016/j.tcs.2022.03.012>; numbering as in arXiv:2107.07834: Theorems 4.1, 4.2, 5.3, 6.1, 7.1–7.4, Proposition 4.5 and Corollaries 4.4, 4.6, 5.1, 5.2, 5.4.
