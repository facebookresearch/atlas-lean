# Incremental thresholded minimum-cost flow in almost-linear total time

There is a deterministic algorithm that, given an incremental directed graph $G = (V, E, \mathbf{u}, \mathbf{c})$ with capacities in $[1, U]$ and costs in $[-C, C]$ where $U, C \le m^{O(1)}$ and $m$ bounds the final number of edges, a demand $\mathbf{d} \in \mathbb{R}^V$ and a threshold $F$ (stated for $F \ge 0$; the incremental cycle-detection application runs the same algorithm with $F = -1$), reports a flow of cost at most $F$ at the first insertion after which such a flow is feasible. The total running time over all insertions is

$$
m\cdot\exp\bigl(O(\log^{167/168} m\log\log m)\bigr).
$$

## Proof sketch

The incremental variant of the l1 IPM keeps a feasible flow on the current graph and treats an inserted edge as a new coordinate with zero flow; it decides the threshold after $m^{1+o(1)}$ calls to a min-ratio cycle solver that must answer correctly on update sequences that depend adaptively on previous outputs. The deterministic data structure *Deterministic fully dynamic approximate min-ratio cycles against any adversary* meets exactly this requirement, so the solver calls cost $m^{1+o(1)}$ in total. Previously only an $m^{1+o(1)}\sqrt{n}$ total bound was known because earlier data structures relied on the restricted update pattern of the static IPM.

## Depends on

- [Incremental thresholded minimum-cost flow problem](incremental-thresholded-min-cost-flow.md)

## Proof depends on

- [Deterministic fully dynamic approximate min-ratio cycles against any adversary](fully-dynamic-min-ratio-cycle-adaptive.md)
- [Potential-reduction l1 IPM: min-cost flow from m^(1+o(1)) approximate min-ratio cycles](../almost-linear-flow-interior-point-method/l1-potential-reduction-ipm.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Simon Meierhans, Maximilian Probst Gutenberg, "Almost-Linear Time Algorithms for Incremental Graphs: Cycle Detection, SCCs, s-t Shortest Path, and Minimum-Cost Flow", STOC (2024), arXiv:2311.18295.
- Jan van den Brand, Yang P. Liu, Aaron Sidford, "Dynamic Maxflow via Dynamic Interior Point Methods", STOC (2023), arXiv:2212.06315.
