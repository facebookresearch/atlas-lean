# Augmenting walks remove two defects

Grow a forest from the defects of a valid labeling, alternating between variables and copies of constraints and recording at each constraint the feasible partner ports (positions whose labels can be flipped together while staying in the relation). If two branches from distinct roots meet, the resulting **augmenting walk** can be flipped: the new labeling is valid and has exactly two fewer defects. If two branches from the same root meet, the meeting determines a **blossom**: a cycle through a common lowest ancestor, with an explicit base and child ports.

## Proof sketch

The six invariants of the forest (unique incoming arcs, saturation of completed scans, no shortcuts, and so on) together with the even delta-matroid exchange property at each constraint make the flips along the walk compatible.

## Depends on

- [Edge CSPs, occurrence labelings and defects](edge-csps-and-defects.md)
- [Delta-matroids and even delta-matroids](../../../../TheoryOfComputation/np-completeness/boolean-constraint-satisfaction/planar-boolean-csp/delta-matroids-and-even-delta-matroids.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), 2019.
