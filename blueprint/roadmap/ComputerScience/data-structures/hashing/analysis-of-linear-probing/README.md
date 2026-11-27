# Analysis of linear probing

Knuth's analysis of hashing with linear probing (1963), his first analysis of an algorithm. Items
are entered into a cyclic table of $N$ cells, each into the first empty cell at or after its hash
address, and all $N^k$ hash sequences are equally likely. The quantities are the mean number of
probes of an insertion (equivalently of an unsuccessful search), $M(N, k)$, and of a successful
search, $T(N, k)$: exact formulas for finite $N$ first, then their limits at a fixed load factor
$\alpha < 1$.

## The model

- [Linear-probing scan with a probe budget](displacement-aux.md)
- [Displacement of a linear-probing insertion](displacement.md)
- [Probes of a linear-probing insertion](probes.md)
- [Cell taken by a linear-probing insertion](insert-cell.md)
- [Occupied cells after a hash sequence](occupancy.md)
- [An insertion into a table that is not full lands on an empty cell](insert-cell-not-mem.md)
- [Linear probing places every item while the table has room](card-occupancy.md)
- [Linear probing commutes with rotations of the table](occupancy-map-rotate.md)
- [An insertion into an empty table has displacement zero](displacement-empty.md)
- [An insertion into an empty table makes one probe](probes-empty.md)

## Exact results

- [Rotational symmetry of linear probing](mul-card-not-mem-occupancy.md)
- [Number of hash sequences that leave a given cell empty](card-not-mem-occupancy.md)
- [Number of hash sequences without overflow](card-lin-success.md)
- [Expected cost of a linear-probing insertion](insertion-cost.md)
- [Expected cost of a successful linear-probing search](successful-search-cost.md)
- [Knuth's auxiliary sums for linear probing](knuth-e.md)
- [Inserting into an empty table costs one probe](insertion-cost-zero.md)
- [A table holding one item is searched in one probe](successful-search-cost-one.md)
- [Knuth's exact mean insertion cost for linear probing](insertion-cost-eq.md)
- [Knuth's exact mean successful-search cost for linear probing](successful-search-cost-eq.md)

## Asymptotics at a fixed load factor

- [Limit of Knuth's sums at a fixed load factor](tendsto-knuth-e.md)
- [Expected cost of an unsuccessful linear-probing search at a fixed load factor](tendsto-insertion-cost.md)
- [Expected cost of a successful linear-probing search at a fixed load factor](tendsto-successful-search-cost.md)

## Related topics

- [Open addressing](../open-addressing/README.md): the keyed open-addressing table with lookup
  and insertion correctness; its [linear-probing probe sequence](../open-addressing/linear-probe.md)
  is the scan analysed here.
- [Parking functions](../../../../Combinatorics/parking-functions/README.md): non-overflow hash
  sequences are partial parking functions, and their count is Pollak's.
- [Average-case running time](../../../randomized-algorithms/average-case-running-time/README.md):
  the expected-cost framework for random inputs used elsewhere in the graph.
- [Amortized analysis](../../amortized-analysis/README.md): the worst-case-over-sequences
  counterpart of the expected costs computed here.
- [Sorting and searching](../../../sorting-and-searching/README.md): searching by comparisons,
  the alternative to hashing for table look-up.
