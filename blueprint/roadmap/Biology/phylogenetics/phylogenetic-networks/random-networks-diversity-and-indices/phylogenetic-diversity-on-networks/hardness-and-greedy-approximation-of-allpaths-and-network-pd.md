# Hardness and greedy approximation of AllPaths-PD and Network-PD

Let $\mathcal{N}$ be a rooted binary phylogenetic network on taxa $X$ with nonnegative arc weights $w$. For $S \subseteq X$:

- **AllPaths-PD** $_{\mathcal{N}}(S) = \sum_{e \in \mathrm{Anc}(S)} w(e)$, summing over arcs on some root-to-$S$ path;
- **Network-PD** $_{\mathcal{N},p}(S) = \sum_e \gamma(S,e)\,w(e)$, where an inheritance proportion $p(e) \in [0,1]$ sits on each reticulation arc and $\gamma(S,\cdot)$ is computed bottom-up: $\gamma(S,e) = 1_{v \in S}$ for a pendant arc into leaf $v$, $\gamma(S,e) = \gamma(S,f_1) + \gamma(S,f_2) - \gamma(S,f_1)\gamma(S,f_2)$ above a tree vertex with child arcs $f_1, f_2$, and $\gamma(S,e) = p(e)\,\gamma(S,f)$ for an arc $e$ into a reticulation with child arc $f$;
- **MaxWeightTree-PD** and **MinWeightTree-PD** $_{\mathcal{N}}(S)$: the maximum and minimum total weight of a connecting subtree (root-rooted arborescence in $\mathcal{N}$ with leaf set $S$).

The optimization problems ask for the maximum score over all $S \subseteq X$ with $|S| = k$.

**Theorem 4.1.** Max-AllPaths-PD is NP-hard, and cannot be approximated in polynomial time with ratio better than $1 - 1/e$ unless P $=$ NP.

**Theorem 4.2.** Max-AllPaths-PD remains NP-hard on normal networks.

**Corollary 4.4.** The greedy algorithm (repeatedly add the taxon of largest marginal gain) is a $(1 - 1/e)$-approximation for Max-AllPaths-PD.

**Proposition 4.5 and Corollary 4.6.** If $\mathcal{N}$ is level-1, there are two weighted connecting trees $T_1, T_2$ (a weighted covering) with $\mathrm{AllPaths\text{-}PD}_{\mathcal{N}}(S) = \mathrm{PD}_{T_1}(S) + \mathrm{PD}_{T_2}(S)$ for all $S$, and Max-AllPaths-PD is solvable in polynomial time on level-1 networks.

**Corollaries 5.1 and 5.2.** Max-Network-PD is NP-hard even on normal networks (take $p \equiv 1$, which recovers AllPaths-PD), and greedy gives a $(1 - 1/e)$-approximation, which is best possible unless P $=$ NP.

So on trees PD is maximized exactly by greedy, but as soon as reticulation lets one arc's features reach several taxa, PD maximization becomes maximum coverage.

## Depends on

- [Greedy maximization of phylogenetic diversity](../../../tree-shapes-characters-and-parsimony/phylogenetic-diversity/greedy-maximization-of-phylogenetic-diversity.md)

## Expansion

The reduction is from Maximum Coverage: take a tree whose weight-1 pendant arcs are the ground elements $e \in E$, and for each set $S_i$ add a reticulation-fed leaf below the arcs of its elements (refining high-degree vertices with weight-0 arcs). A set of $k$ leaves then has AllPaths-PD equal to the number of covered elements, so exact or better-than-$(1-1/e)$ solutions would transfer. Subdividing reticulation arcs and attaching weight-adjusted leaves makes the construction normal. Both AllPaths-PD and Network-PD are monotone submodular set functions; for Network-PD, $\gamma(S,e)$ is the probability that a feature arising on $e$ reaches some taxon of $S$, so inclusion–exclusion gives $\gamma(A\cup B,e) \le \gamma(A,e) + \gamma(B,e) - \gamma(A\cap B,e)$, and the Nemhauser–Wolsey–Fisher bound applies to greedy. On level-1 networks, cycles are disjoint, so each reticulation's two incoming paths can be split between two trees, and the joint maximization of $\mathrm{PD}_{T_1} + \mathrm{PD}_{T_2}$ over $k$-subsets is solved in polynomial time.

## Sources

- Magnus Bordewich, Charles Semple and Kristina Wicke, "On the complexity of optimising variants of phylogenetic diversity on phylogenetic networks", Theoretical Computer Science 917 (2022), 66–80, <https://doi.org/10.1016/j.tcs.2022.03.012>; numbering as in arXiv:2107.07834: Theorems 4.1, 4.2, 5.3, 6.1, 7.1–7.4, Proposition 4.5 and Corollaries 4.4, 4.6, 5.1, 5.2, 5.4.
