# MPC with linear memory simulates the congested clique

Any $T$-round congested clique algorithm on an $n$-vertex input graph with $m$ edges can be simulated in $O(T)$ rounds of the MPC model with local memory $S = O(n)$ words and total memory $O(m + n)$ words, provided each congested clique processor sends and receives $O(\deg(v) + 1)$ message volume in each round (as holds for many graph algorithms); without the volume assumption, $O(T)$ rounds suffice with total memory $O(n^2)$.

## Proof sketch

Assign each congested clique processor, together with its incident edges, to machines so that each machine holds $O(n)$ words; a vertex of high degree is split over several machines coordinated through a constant-depth aggregation tree. One congested clique round is emulated by one MPC round in which each machine sends the messages of its hosted processors, since the per-machine communication bound $S$ dominates the volume each processor sends and receives.

## Depends on

- [The massively parallel computation model](massively-parallel-computation-model.md)
- [The congested clique model](../../concurrent-systems-and-protocols/distributed-execution-models/congested-clique-algorithms/the-congested-clique-model.md)

## Proof depends on

- [The massively parallel computation model](massively-parallel-computation-model.md)

## Sources

- S. Behnezhad, M. Derakhshan, M. T. Hajiaghayi, "Brief Announcement: Semi-MapReduce Meets Congested Clique", arXiv:1802.10297 (2018).
