# Approximation schemes for maximum agreement relation editing

Use the relation graphs, satisfiability ($P_4$-freeness) and $S$-consistency of weighted cograph editing of orthology relation graphs, now unweighted. For a relation graph $R = (\Gamma, E_R)$ with $n = |\Gamma|$ and a candidate $R' = (\Gamma, E_{R'})$, the **agreement value** counts preserved orthologies and paralogies:

$$A(R', R) = |E_R \cap E_{R'}| + |\bar E_R \cap \bar E_{R'}| .$$

**MaxES** asks for a satisfiable $R'$ maximizing $A(R', R)$; **MaxEC** asks for an $S$-consistent $R'$ maximizing it.

**Lemma 6.** For both problems the optimum agreement is at least $n^2/8$.

**Theorem.** MaxES and MaxEC admit polynomial-time approximation schemes: for every $\varepsilon > 0$ there is a polynomial algorithm returning a satisfiable (respectively $S$-consistent) relation graph with agreement at least $(1 - \varepsilon)\,\mathrm{OPT}$.

## Depends on

- [Weighted cograph editing of orthology relation graphs](weighted-cograph-editing-of-orthology-relation-graphs.md)

## Expansion

The empty graph and the complete graph are both satisfiable and consistent, and every pair agrees with exactly one of them, so one achieves agreement at least half the number of pairs, giving Lemma 6. Because the optimum is $\Omega(n^2)$, the known additive $\varepsilon n^2$ approximation for cograph editing converts into a multiplicative PTAS for MaxES. That solution need not be $S$-consistent; for MaxEC one compresses an optimal gene tree into a tree with a bounded number of leaf classes losing $O(n^2/k)$ agreement, enumerates all compressed shapes, event labels and allowed species sets, solves each resulting assignment problem by smooth polynomial integer programming, and rebuilds an $S$-consistent DS-tree from the best compressed tree. Minimizing edits and maximizing agreement have the same optima but very different approximability: the weighted minimization is not constant-factor approximable under the unique games conjecture.

## Sources

- R. Dondi, M. Lafond, N. El-Mabrouk, "Approximating the correction of weighted and unweighted orthology and paralogy relations", Algorithms for Molecular Biology 12 (2017) 4, problem statements MaxES and MaxEC, Lemma 6 and the PTAS sections, <https://doi.org/10.1186/s13015-017-0096-x>, PMCID PMC5346272.
