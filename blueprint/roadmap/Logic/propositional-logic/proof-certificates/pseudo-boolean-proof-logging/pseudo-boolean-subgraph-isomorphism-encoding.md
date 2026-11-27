# Pseudo-Boolean encoding of subgraph isomorphism and certified answers

For a pattern graph $P$ and target graph $T$, the encoding has variables $x_{p,t}$ (pattern vertex $p$ mapped to target vertex $t$) with constraints that every $p$ is mapped to exactly one $t$, every $t$ receives at most one $p$, and for every edge $pq$ of $P$ and every $t$, $x_{p,t}$ implies $\sum_{t' \in N_T(t)} x_{q,t'} \ge 1$. Its solutions are exactly the injective homomorphisms (non-induced subgraph embeddings) of $P$ into $T$. Hence a VeriPB proof accepted for the encoding with conclusion UNSAT certifies that $T$ contains no copy of $P$, and one with conclusion SAT that it does.

## Proof sketch

Exactly-one and at-most-one constraints make solutions injective maps; the adjacency constraints say edges map to edges. Apply soundness of the checker.

## Depends on

- [Pseudo-Boolean constraints in normalized form](pseudo-boolean-constraints.md)

## Proof depends on

- [Soundness of the VeriPB kernel proof format](veripb-kernel-soundness.md)
- [SUBGRAPH ISOMORPHISM is NP-complete](../../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/subgraph-isomorphism/subgraph-isomorphism-np-complete.md)

## Sources

- S. Gocht, C. McCreesh, M. O. Myreen, J. Nordström, A. Oertel and Y. K. Tan, "End-to-End Verification for Subgraph Solving", Proceedings of the 38th AAAI Conference on Artificial Intelligence, 2024: Figure 2 (non-induced subgraph isomorphism) and Section 3.
