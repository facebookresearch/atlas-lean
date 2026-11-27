# Triplet supertree local search

**Problem.** For a rooted tree $T$ let $\mathrm{Tr}(T)$ be the set of rooted triplets $ab|c$ it displays. For a profile $P = (T_1, \dots, T_n)$ of rooted input trees and a supertree $T^*$ on all their leaves, the **triplet-similarity score** is

$$S(P, T^*) = \sum_{i=1}^n |\mathrm{Tr}(T_i) \cap \mathrm{Tr}(T^*)|,$$

and the **triplet supertree problem** asks for $T^*$ maximizing it. The problem is NP-hard, so it is attacked by hill climbing over subtree prune and regraft (SPR) and tree bisection and reconnection (TBR) neighbourhoods.

**Triplet summation.** Let $\sigma_P(ab|c) = \sum_i [\![ ab|c \in \mathrm{Tr}(T_i)]\!]$ count input trees displaying $ab|c$, extended to pairwise disjoint leaf sets by $\sigma_P(AB|C) = \sum_{a\in A, b \in B, c\in C}\sigma_P(ab|c)$, and for pairwise non-nested nodes $u, v, w$ of $T$ let $\sigma_{P,T}(uv|w) = \sigma_P(\mathrm{Le}(T_u)\mathrm{Le}(T_v)|\mathrm{Le}(T_w))$. An **immediate triplet** $yz \bowtie v$ at node $v$ means $y, z$ are siblings whose parent is a sibling of $v$.

**Lemma (score change of one SPR).** If $yz \bowtie v$ is an immediate triplet in $T$ and $T' = \mathrm{SPR}_T(v, y)$ regrafts $T_v$ onto the edge above $y$, then

$$S(P,T') - S(P,T) = \sigma_{P,T}(vy|z) - \sigma_{P,T}(yz|v).$$

The same difference governs the comparison of regrafting $v$ above a node $b$ with children $y, z$ versus above $y$.

**Theorem (complexity).** After a one-time $O(kn^3)$ pass that counts how many of the $k$ input trees display each triplet over the $n$ taxa, the best tree in the full SPR neighbourhood and in the full TBR neighbourhood of a supertree can each be found in $O(n^3)$ time, compared with $O(kn^4)$ and $O(kn^5)$ for naive evaluation.

## Depends on

- [Rooted triplet](../../splits-compatibility-ultrametrics-and-upgma/triplet.md)

## Expansion

Moving $T_v$ one step down past $z$ changes the resolution of only the triplets with one leaf in each of $T_v$, $T_y$, $T_z$: they switch from $yz|v$ to $vy|z$, which is the lemma. Regrafting further away is a chain of such moves, so the score of every regraft position of a pruned subtree is a prefix sum along the tree, computed with $O(n^3)$ preprocessed triplet counts by dynamic programming. A TBR move is an SPR followed by re-rooting the pruned subtree, and the best re-rooting of each subtree can be chosen independently of the regraft point, which keeps TBR at the same cubic bound.

## Sources

- H. T. Lin, J. G. Burleigh, O. Eulenstein, "Triplet supertree heuristics for the tree of life", BMC Bioinformatics 10 (Suppl 1): S8 (2009), Definitions 1–9, Theorem 1, Lemmas 1–6 (Eqs 2–3), <https://doi.org/10.1186/1471-2105-10-s1-s8>, PMCID PMC2648750.
