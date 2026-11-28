# Minimum spanning trees in O(1) rounds of the congested clique, deterministically

In the congested clique, a minimum spanning tree (forest) of an $n$-vertex weighted input graph with weights of $O(\log n)$ bits can be computed in $O(1)$ rounds: first by a randomized algorithm, and subsequently by a deterministic algorithm. Earlier deterministic bounds were $O(\log\log n)$ rounds via Borůvka-style phases in which the minimum growable fragment size $s$ grows to at least $s(s+1)$.

## Proof sketch

Both algorithms start from the reduction of Hegeman et al., whose randomized step (KKT-style edge sampling and filtering of $F$-heavy edges) reduces one MST instance to two MST instances with $O(n^{3/2})$ edges each; an MST of an $O(n^{3/2})$-edge graph then reduces to $O(\sqrt n)$ nested connected-components instances. The randomized algorithm solves these in parallel in $O(1)$ rounds with a new connected-components algorithm: it collects many random sparse samples of $O(n)$ edges, each at one processor by Lenzen routing, computes their spanning forests locally, and combines them through randomly chosen leaders. The deterministic algorithm replaces the randomized step by Korhonen's sparsification. Given a $\Delta$-partition of the vertices (blocks of size $O(n/\Delta)$ with $O(n/\Delta)$ edges between every two blocks), it groups the blocks into $\sqrt\Delta$ super-blocks, gathers the $O(n)$ edges between each pair of super-blocks at one processor and keeps only their minimum spanning forest. By the cycle property the MST is preserved, and the result has a $\sqrt\Delta$-partition. A degree-reducing preprocessing gives an $O(m/n)$-partition, so one sparsification leaves $O(\sqrt{mn})$ edges; together with a deterministic connected-components algorithm this gives the $O(1)$ deterministic bound.

## Depends on

- [The congested clique model](the-congested-clique-model.md)

## Proof depends on

- [Lenzen's deterministic constant-round routing and sorting in the congested clique](congested-clique-constant-round-routing.md)

## Sources

- T. Jurdziński, K. Nowicki, "MST in O(1) Rounds of Congested Clique", SODA 2018, arXiv:1707.08484, Section 2.
- K. Nowicki, "A Deterministic Algorithm for the MST Problem in Constant Rounds of Congested Clique", STOC 2021, arXiv:1912.04239, Theorem 2.1 and Section 3.
- Z. Lotker, B. Patt-Shamir, E. Pavlov, D. Peleg, "Minimum-Weight Spanning Tree Construction in O(log log n) Communication Rounds", SIAM Journal on Computing 35(1) (2005); SPAA 2003.
- T. Jurdziński, K. Nowicki, "MSF and Connectivity in Limited Variants of the Congested Clique", arXiv:1703.02743, Section 4.1 (Lemma 1 and the phase sequence $\mu_1 = 1$, $\mu_i = \mu_{i-1}(\mu_{i-1} + 1)$ of Lotker et al.).
- J. W. Hegeman, S. V. Pemmaraju, V. B. Sardeshmukh, "Near-Constant-Time Distributed Algorithms on a Congested Clique", arXiv:1408.2071, Section 1.1.
