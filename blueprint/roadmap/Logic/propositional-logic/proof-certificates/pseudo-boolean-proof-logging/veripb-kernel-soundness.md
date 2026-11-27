# Soundness of the VeriPB kernel proof format

Consider a VeriPB kernel proof for a pseudo-Boolean instance (constraints and an optional linear objective) built from the rules: cutting planes derivations, RUP steps, redundance-based and dominance-based strengthening with witnesses, solution logging and objective-improving steps, and deletions within the core set. If a sound checker accepts the proof with conclusion UNSAT then the instance has no solution; with conclusion SAT a solution exists; with conclusion BOUNDS $(\mathit{lb}, \mathit{ub})$ the optimum lies between them, every logged solution certifying an upper bound.

## Proof sketch

Each rule preserves the validity invariant of Bogaerts et al.: the core constraints have the same optimal value as the input instance (or are equisatisfiable with it), and every solution of the core can be turned into one, no worse, of the core and derived constraints; the conclusions read off this invariant.

## Depends on

- [Pseudo-Boolean cutting planes with saturation and weakening](pseudo-boolean-cutting-planes-rules.md)
- [Reverse unit propagation for pseudo-Boolean constraints](pseudo-boolean-reverse-unit-propagation.md)

## Proof depends on

- [Soundness of redundance-based strengthening with witnesses](redundance-based-strengthening-soundness.md)
- [Soundness and refutation completeness of cutting planes](../../../proof-theory/cutting-planes/cutting-planes-soundness-and-completeness.md)

## Sources

- B. Bogaerts, S. Gocht, C. McCreesh and J. Nordström, "Certified Dominance and Symmetry Breaking for Combinatorial Optimisation", Journal of Artificial Intelligence Research 77, 1539–1589, 2023.
- S. Gocht and J. Nordström, "Certifying Parity Reasoning Efficiently Using Pseudo-Boolean Proofs", Proceedings of the 35th AAAI Conference on Artificial Intelligence, 2021.
- S. Gocht, C. McCreesh, M. O. Myreen, J. Nordström, A. Oertel and Y. K. Tan, "End-to-End Verification for Subgraph Solving", Proceedings of the 38th AAAI Conference on Artificial Intelligence, 2024.
