# NP-hardness of parsimonious clone tree integration

**Proportion matrices.** An $m \times n$ matrix $U = [u_{p,\ell}]$ is a *proportion matrix* for $n$ clones in $m$ samples if $u_{p,\ell} \ge 0$ and $\sum_{\ell} u_{p,\ell} = 1$ for every sample $p$. Two features (e.g. SNVs and CNAs) give clone sets $\Pi_1 = [n_1]$ and $\Pi_2 = [n_2]$ with proportion matrices $U_1, U_2$. A set of joint clones $\Pi \subseteq \Pi_1 \times \Pi_2$ with projections $\pi_1, \pi_2$ and proportions $U$ is *consistent* with $U_1, U_2$ if

$$u^{(1)}_{p,i} = \sum_{\ell : \pi_1(\ell) = i} u_{p,\ell}, \qquad u^{(2)}_{p,j} = \sum_{\ell : \pi_2(\ell) = j} u_{p,\ell}\qquad \text{for all } p, i, j.$$

**Problem PCI (parsimonious clone integration).** Given $U_1, U_2$, find the smallest $\Pi \subseteq \Pi_1 \times \Pi_2$ and proportions $U$ consistent with $U_1, U_2$.

**Refinement of clone trees.** A clone tree $T$ on $\Pi$ refines clone trees $T_1$ on $\Pi_1$ and $T_2$ on $\Pi_2$ if each edge $(i,i')$ of $T_1$ appears as exactly one edge $((i,j),(i',j))$ of $T$, each edge $(j,j')$ of $T_2$ appears as exactly one edge $((i,j),(i,j'))$ of $T$, and every edge of $T$ is of one of these two kinds.

**Problem PCTI (parsimonious clone tree integration).** Given $(U_1,T_1)$ and $(U_2,T_2)$, find $\Pi$, a refinement $T$ of $T_1$ and $T_2$, and proportions $U$ minimizing

$$J(U,U_1,U_2) = \sum_{p=1}^m\sum_{i=1}^{n_1}\Big|u^{(1)}_{p,i} - \sum_{\ell:\pi_1(\ell)=i} u_{p,\ell}\Big| + \sum_{p=1}^m\sum_{j=1}^{n_2}\Big|u^{(2)}_{p,j} - \sum_{\ell:\pi_2(\ell)=j} u_{p,\ell}\Big|.$$

**Structural facts.**
- $\max(S(U_1), S(U_2)) \le |\Pi| \le n_1 n_2$ for PCI, where $S(U)$ is the number of clones with positive proportion in some sample; the upper bound is attained greedily by assigning $\min(u^{(1)}_{p,i}, u^{(2)}_{p,j})$ to each pair in turn.
- For a fixed $\Pi$, deciding whether a consistent $U$ exists is a maximum-flow problem (single-commodity for $m = 1$), hence polynomial.
- Any feasible PCTI tree has root $(r(T_1), r(T_2))$, changes exactly one coordinate along each edge, and has exactly $n_1 + n_2 - 1$ vertices; it is a two-character cladistic multi-state perfect phylogeny.

**Theorem 1.** PCI is NP-hard, even for $m = 1$ sample.

**Theorem 2.** PCTI is NP-hard, even for $m = 1$ sample.

## Proof depends on

- [3-PARTITION is NP-complete](../../../TheoryOfComputation/np-completeness/number-and-packing-problems/3-partition-problem/three-partition-np-complete.md)
- [Edmonds-Karp computes a maximum flow and a minimum cut](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/edmonds-karp-algorithm/edmonds-karp-max-flow-min-cut.md)

## Expansion

Both proofs reduce from 3-PARTITION: given $B$ and $3q$ integers $a_i \in (B/4, B/2)$ summing to $Bq$, decide whether they split into $q$ triples each summing to $B$. For PCI, take $u^{(1)}_{1,i} = a_i/(Bq)$ for $i \in [3q]$ and $u^{(2)}_{1,j} = 1/q$ for $j \in [q]$; each first-feature clone must pair with at least one second-feature clone, so a consistent solution with at most $3q$ joint clones pairs every $i$ with exactly one $j$, and the column sums force each $j$ to collect integers summing to $B$ (Lemma 1). For PCTI, a root clone $0$ with proportion $0$ is added to both clone sets, and an error-free refinement with $4q+1$ clones exists iff the 3-PARTITION instance is solvable (Lemma 2). Exact solutions are computed in practice by mixed integer linear programs.

## Sources

- P. Sashittal, S. Zaccaria, M. El-Kebir, "Parsimonious clone tree integration in cancer", Algorithms for Molecular Biology 17 (2022) 3, Definitions 1–3, Problems 1–3, Observations 1–4, Theorems 1–2 and Lemmas 1–2, <https://doi.org/10.1186/s13015-022-00209-9>, PMCID PMC8919608.
