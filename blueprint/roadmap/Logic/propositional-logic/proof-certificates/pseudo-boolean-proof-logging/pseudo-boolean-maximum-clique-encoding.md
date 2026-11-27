# Pseudo-Boolean encoding of maximum clique and certified clique bounds

For a graph $G$ on vertices $[n]$, the pseudo-Boolean encoding has a variable $x_v$ per vertex, a constraint $\bar x_u + \bar x_v \ge 1$ for every non-adjacent pair $u \ne v$, and the objective $\min \sum_v \bar x_v$ (equivalently maximize $\sum_v x_v$). Its solutions are exactly the indicator vectors of cliques of $G$, with objective value $n - |K|$. Consequently a VeriPB proof accepted for this encoding with conclusion BOUNDS $(\mathit{lb}, \mathit{ub})$ certifies $n - \mathit{ub} \le \omega(G) \le n - \mathit{lb}$, and equal bounds certify the clique number exactly.

## Proof sketch

A 0/1 vector satisfies all non-edge constraints iff its support contains no non-adjacent pair; combine with soundness of the checker for BOUNDS conclusions.

## Depends on

- [Pseudo-Boolean constraints in normalized form](pseudo-boolean-constraints.md)
- [Soundness of the VeriPB kernel proof format](veripb-kernel-soundness.md)

## Proof depends on

- [CLIQUE is NP-complete](../../../../TheoryOfComputation/np-completeness/graph-covering-and-domination/clique-independent-set-and-vertex-cover/part-08/clique-dec-np-complete.md)

## Sources

- S. Gocht, C. McCreesh, M. O. Myreen, J. Nordström, A. Oertel and Y. K. Tan, "End-to-End Verification for Subgraph Solving", Proceedings of the 38th AAAI Conference on Artificial Intelligence, 2024: Section 3 (verified clique encoder and bound conclusions).
