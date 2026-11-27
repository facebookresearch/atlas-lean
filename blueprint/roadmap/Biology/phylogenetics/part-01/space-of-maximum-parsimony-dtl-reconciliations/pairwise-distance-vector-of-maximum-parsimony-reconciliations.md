# Pairwise distance vector of maximum parsimony reconciliations

For a DTL instance with species tree vertex count $n = |V_S|$, gene tree vertex count $m = |V_G|$ and positive transfer and loss costs, identify each MPR $R$ with its event set $E(R)$ in the reconciliation graph and use the symmetric distance $d(R_1, R_2) = |E(R_1) \oplus E(R_2)|$. The **pairwise distance vector** $v$ has $v[i]$ equal to the number of pairs of MPRs at distance exactly $i$. Then $v[0]$ is the number of MPRs and the largest $i$ with $v[i] > 0$ is the diameter of MPR space.

**Theorem (PDV algorithm).** $v$ can be computed exactly in worst-case time $O(n^4 m^2 \log m)$, independent of the number of MPRs.

For a gene vertex $g$ and species vertices $s_1, s_2$, let $\mathrm{PDV}_g(s_1, s_2)$ count pairs of subtraversals rooted at $(g, s_1)$ and $(g, s_2)$ by the number of event nodes in which they differ; then $v = \sum \mathrm{PDV}_{r_G}(s_1, s_2)$ over pairs of sources. These vectors satisfy a mutual recursion with two helper tables (pairs that both start with a speciation, duplication or transfer event, and pairs where only the ancestral one does), built from three vector operations: sum, shift $\sigma^j$ (adding $j$ to every distance) and convolution $(u * v)[i] = \sum_{j \le i} u[j]\,v[i-j]$. Two different non-loss first events contribute a shift by 2, a loss present in only one subtraversal a shift by 1, and the two child subproblems combine by convolution, with multiplicities $1, 2, 4$ according to how many child mapping nodes the two events share.

**Lemmas.** (1) Every MPR has $O(m)$ events, so all vectors have dimension $O(m)$ and a convolution costs $O(m \log m)$ by the fast Fourier transform. (2) Each mapping node has $O(n)$ speciation, duplication and transfer event children. (3) The table with $O(n^2 m)$ entries, each a sum of $O(n^2)$ convolutions, dominates the cost, giving $O(n^4 m^2 \log m)$.

Replacing the shift by 2 with the species-tree distance $d_S(s_1, s_2)$ handles the path distance $\sum_g d_S(\Phi_1(g), \Phi_2(g))$, whose diameter is $O(mn)$, in time $O(n^5 m^2 \log(mn))$.

## Depends on

- [Reconciliation graph of maximum parsimony DTL reconciliations](reconciliation-graph-of-maximum-parsimony-reconciliations.md)

## Expansion

Distances between traversals are additive over the event choices made at each mapping node: once the first events below $(g, s_1)$ and $(g, s_2)$ are fixed, the remaining differences split into independent contributions from the two gene children, and the distribution of a sum of independent counts is the convolution of their distributions. Processing the acyclic reconciliation graph bottom-up therefore yields the full distribution without enumerating MPRs; the authors validated the recursion against brute force on all instances with up to six leaves.

## Sources

- S. Santichaivekin, R. Mawhorter, R. Libeskind-Hadas, "An efficient exact algorithm for computing all pairwise distances between reconciliations in the duplication-transfer-loss model", BMC Bioinformatics 20(Suppl 20):636 (2019), Eq. (1), the PDV recursions, Lemmas 1-3 and the section on other distance metrics, <https://doi.org/10.1186/s12859-019-3203-9>, PMCID PMC6915856.