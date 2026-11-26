# An exhausted forest search certifies optimality

If the forest search exhausts every incidence of every visited variable without finding an augmentation or a blossom, and every constraint is a nonempty even delta-matroid on its argument positions, then the current valid labeling has the minimum number of defects among all valid labelings.

## Proof sketch

Compare with any valid labeling: saturation of the scans bounds local disagreements at each constraint by one-sided exchange, while fresh roots and unique children bound the global changes; counting the two bounds shows the other labeling cannot have fewer defects.

## Depends on

- [Edge CSPs, occurrence labelings and defects](edge-csps-and-defects.md)
- [Delta-matroids and even delta-matroids](../../../../TheoryOfComputation/np-completeness/satisfiability/planar-boolean-csp/delta-matroids-and-even-delta-matroids.md)
- [Augmenting walks remove two defects](edge-csp-augmenting-walks.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), 2019.
