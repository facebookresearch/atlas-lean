# Static cell-probe structure with space $S$ and query time $t$

A *static data structure problem* is a function $f : \mathcal{D} \times \mathcal{Q} \to \mathcal{A}$ from inputs and queries to answers. A *static cell-probe structure* for $f$ with space $S$ and query time $t$ maps each input $D \in \mathcal{D}$ to a memory of $S \le 2^w$ cells of $w$ bits, so that one cell can hold the address of any cell, and answers each query $q \in \mathcal{Q}$ by adaptively probing at most $t$ cells and then outputting $f(D, q)$, with all computation free.

## Depends on

- [The cell-probe model](../range-query-structures/advanced-data-structures/the-cell-probe-model.md)

## Sources

- Andrew C. Yao, "Should Tables Be Sorted?", Journal of the ACM 28(3) (1981).
- Kasper Green Larsen, "Higher Cell Probe Lower Bounds for Evaluating Polynomials", FOCS (2012).
