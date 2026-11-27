# Multi-gene reconciliation with segmental duplications

**Setting.** Let $S$ be a rooted binary species tree and $\mathcal G$ a forest of rooted binary gene trees whose leaves are labelled by species. A reconciliation $\alpha$ maps every gene node $u$ to a species node $\alpha_r(u)$ and an event $\alpha_e(u) \in \{S, D, C\}$ (speciation, duplication, contemporary leaf) such that leaves map to their species, a speciation $u$ with children $u_1, u_2$ has $\alpha_r(u) = \mathrm{LCA}_S(\alpha_r(u_1), \alpha_r(u_2))$ with $\alpha_r(u_1), \alpha_r(u_2)$ incomparable, and a duplication satisfies $\alpha_r(u) \ge \alpha_r(u_1), \alpha_r(u_2)$ (evolution cannot go back in time). The LCA mapping $\mu$ is the reconciliation mapping each node as low as possible. Let $l(\alpha)$ be the number of gene losses implied by $\alpha$.

**Segmental duplication count.** For $s \in V(S)$ let $G[\alpha, s]$ be the forest induced by the duplications mapped to $s$. Duplications in one segmental event must be pairwise incomparable, and the minimum number of segmental events explaining them is the minimum number of antichains covering $G[\alpha,s]$, which equals its height $h_\alpha(s)$. Define $\hat d(\alpha) = \sum_{s} h_\alpha(s)$ and, for costs $\delta$ (duplication) and $\lambda$ (loss),

$$\mathrm{cost}_{SD}(\mathcal G, S, \alpha) = \delta\, \hat d(\alpha) + \lambda\, l(\alpha).$$

The problem MPRST-SD asks for a reconciliation minimizing this cost.

**Theorem.**
1. If $\lambda \ge \delta$, the LCA mapping $\mu$ is an optimal reconciliation; if $\lambda > \delta$ it is the unique optimum.
2. If $\delta > \lambda$, MPRST-SD is NP-hard, already for $\lambda = 0$ and even when $\mathcal G$ is a single gene tree.
3. (Fixed-parameter tractability.) For $\lambda > 0$, an optimal reconciliation with at most $d$ segmental duplications can be found in time $O\big(\lceil \delta/\lambda\rceil^{d} \cdot n \cdot \delta/\lambda\big)$, where $n$ is the input size.

## Depends on

- [Is LCAReconciliation](../../../not-yet-classified/lcareconciliation/is-lcareconciliation.md)

## Expansion

Changing a feasible duplication into a speciation never increases cost, so optimal reconciliations take speciations wherever allowed. The **shift-down lemma** quantifies the trade-off: remapping a node one level lower along its path saves at least one loss per level, so if a minimal unresolved node were placed more than $\lceil \delta/\lambda\rceil$ ancestors above its lowest possible image $\mu_\alpha(v)$, moving it down would save more than $\delta$ in losses while adding at most one segmental duplication. This bounds the branching factor of a bottom-up search by $\lceil\delta/\lambda\rceil$, and each branch either adds a segmental duplication or is forced, giving the FPT bound. When losses are at least as expensive as duplications, pushing anything above its LCA image only adds losses, which is part 1. Hardness for $\delta > \lambda$ comes from a reduction in which grouping duplications into few antichains encodes a combinatorial covering problem; joining the trees of the forest under long speciation paths transfers it to a single tree.

## Sources

- R. Dondi, M. Lafond, C. Scornavacca, "Reconciling multiple genes trees via segmental duplications and losses", Algorithms for Molecular Biology 14:7 (2019), Definition 1, Problem 1, Lemmas 1 and 6, Theorems 1–4, <https://doi.org/10.1186/s13015-019-0139-6>, PMCID PMC6425616.
