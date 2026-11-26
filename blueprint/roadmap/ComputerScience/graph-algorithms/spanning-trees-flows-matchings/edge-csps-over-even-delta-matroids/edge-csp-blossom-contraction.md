# Blossom contraction preserves improvability

Contracting a blossom found by the forest search into a single new constraint (whose relation is induced by the blossom's constraints and internal variables) yields a smaller edge CSP whose constraints are again even delta-matroids and whose valid labelings correspond to those of the original instance with the same number of defects (after the blossom's preparation flip). An improvement of the contracted instance lifts to an improvement of the original, and an optimal labeling of the contracted instance transfers to an optimal labeling of the original.

## Depends on

- [Edge CSPs, occurrence labelings and defects](edge-csps-and-defects.md)
- [Augmenting walks remove two defects](edge-csp-augmenting-walks.md)

## Proof depends on

- [Local contraction preserves even delta-matroids](../../../../TheoryOfComputation/np-completeness/satisfiability/planar-boolean-csp/local-contraction-preserves-even-delta-matroids.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), 2019.
