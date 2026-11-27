# Optimal capping and the DCJ-indel distance of natural genomes

**Natural genomes.** When common markers may occur several times, write $\Phi_A(m), \Phi_B(m)$ for the multiplicities of marker $m$. Matching occurrences of each common marker (as many as $\min\{\Phi_A(m),\Phi_B(m)\}$) and treating unmatched copies as exclusive turns $A, B$ into matched singular genomes $A^\ddagger, B^\ddagger$ with $n^* = \sum_{m}\min\{\Phi_A(m),\Phi_B(m)\}$ common markers. The DCJ-indel distance of natural genomes is

$$d_{\mathrm{DCJ}}^{\mathrm{id}}(A,B) = \min_{(A^\ddagger,B^\ddagger)} d_{\mathrm{DCJ}}^{\mathrm{id}}(A^\ddagger,B^\ddagger).$$

Computing it is NP-hard.

**Theorem (optimal capping).** Let $\kappa_A, \kappa_B$ be the numbers of linear chromosomes of singular genomes $A, B$. There is an optimal capping (adding artificial common markers (caps) that circularize every linear chromosome without changing the DCJ-indel distance) using exactly

$$p^* = \max\{\kappa_A,\kappa_B\} \text{ caps and } a^* = |\kappa_A - \kappa_B| \text{ artificial adjacencies between caps.}$$

**Theorem (decomposition formula).** In the capped multi-relational diagram $MR^\circ(A,B)$ (all extremity edges between equal extremities of equal markers, $4p^*$ cap extremities joined by cap extremity edges), a *capped consistent decomposition* $Q[S,P]$ is the cycle cover induced by a maximal sibling set $S$ (a matching of occurrences) and a maximal capping set $P$. Then

$$d_{\mathrm{DCJ}}^{\mathrm{id}}(A,B) = n^* + p^* - \max_{S, P} w(Q[S,P]), \qquad w(Q) = c_Q - \sum_{C \in Q}\lambda(C),$$

with $c_Q$ the number of $AB$-cycles of $Q$ (circular singletons, counted by $s_Q$, are not cycles of this count). Writing $\aleph(C)$ for the number of *transitions* of a cycle (indel-free subpaths flanked by an indel edge of $A$ and one of $B$) and $r(C) = 1$ iff $\Lambda(C) \ge 1$,

$$\lambda(C) = \frac{\aleph(C)}{2} + r(C), \qquad w(Q) = \tilde c^{\,r}_Q - \frac{\aleph_Q}{2} - s_Q,$$

where $\tilde c^{\,r}_Q$ counts indel-free cycles, $\aleph_Q$ all transitions and $s_Q$ circular singletons. This weight is linear in edge and label indicators, giving an integer linear program for the distance.

## Depends on

- [DCJ-indel distance and indel-potential of singular genomes](dcj-indel-distance-and-indel-potential.md)

## Expansion

Capping: each chained recombination group of the linear formula is closed into one $AB$-cycle by caps; after the greedy assignment all unbalanced groups are over-represented in the same genome (Proposition 1), and each is closed either by a leftover indel-free path of the other genome or by an artificial adjacency (Proposition 2), so the cap count matches the canonical case. Since every maximal capping set uses exactly $p^*$ caps and all adjacencies, for each sibling set the best capping set realizes an optimal capping of $A^\ddagger_S, B^\ddagger_S$, so $w(D[S]) = \max_P w(Q[S,P])$ (Theorem 3), and minimizing over $S$ gives the formula. On a cycle with at least two runs, $\aleph(C) = \Lambda(C)$ is even, which yields $\lambda = \aleph/2 + 1$; a single run gives $\aleph = 0$, $\lambda = 1$.

## Sources

- L. Bohnenkämper, M. D. V. Braga, D. Doerr, J. Stoye, "Computing the rearrangement distance of natural genomes", Journal of Computational Biology 28 (2021), Section 4 (multi-relational diagram, consistent decompositions), Section 5 (Propositions 1–2, Theorems 2–3) and Section 6 (Proposition 3, ILP), <https://doi.org/10.1089/cmb.2020.0434>, PMCID PMC8082732.
