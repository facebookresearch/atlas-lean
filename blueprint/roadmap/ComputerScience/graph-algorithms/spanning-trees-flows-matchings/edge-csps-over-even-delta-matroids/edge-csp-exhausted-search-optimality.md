# An exhausted forest search certifies optimality

If every constraint is an even delta-matroid and the forest search for a valid labeling $f$ stops because every incidence of every variable in the forest has been used, without ever meeting two branches (no augmenting walk and no blossom), then $f$ is optimal: it has the minimum number of defects among all valid labelings.

## Proof sketch

If some valid labeling $g$ has fewer defects than $f$, the even delta-matroid exchange property at each constraint turns $f \triangle g$ into an augmenting walk for $f$. One then shows by induction along any walk that starts at a defect and keeps every intermediate labeling valid that each of its constraint-to-variable steps is an arc of the final forest. The last step of the augmenting walk enters a defect, which is a root and already has outgoing arcs to both its constraints, a contradiction.

## Depends on

- [Edge CSPs, occurrence labelings and defects](edge-csps-and-defects.md)
- [Delta-matroids and even delta-matroids](../../../../TheoryOfComputation/np-completeness/boolean-constraint-satisfaction/planar-boolean-csp/delta-matroids-and-even-delta-matroids.md)
- [Augmenting walks remove two defects](edge-csp-augmenting-walks.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019, Lemma 31 and Lemma 45.
