# Simulation of Word-RAM data structures by cell-probe schemes

Let a Word-RAM data structure with word size $w$ use the memory block $[b, b+S)$ and $r$ registers, of which $p$ are persistent between operations, and suppose every operation halts within $t$ instructions. Then there is a deterministic cell-probe scheme with $S + p$ cells of $w$ bits that returns the same answers on every history and makes $O(t + p)$ probes per operation (reload the persistent registers, simulate, spill them back). Alternatively, packing all persistent registers into one extra cell, which then has width $\max(p, 1) \cdot w$ instead of $w$, gives $S + 1$ cells and $O(t + 1)$ probes per operation. The same holds for randomized and Las Vegas executions, with the bound on expected instructions becoming a bound on expected probes.

In particular, any lower bound $L$ on expected probes per operation for cell-probe schemes with the given space translates into a lower bound of $\Omega(L) - O(p)$ expected instructions for the Word-RAM implementation.

## Proof sketch

Each instruction reads or writes a constant number of memory words, each of which becomes one probe; register-only instructions are free in the cell-probe model. Non-persistent registers are recomputed inside each operation, so only persistent registers must be carried in cells, and they are read once at the start and written once at the end of each operation.

## Depends on

- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [Deterministic dynamic cell-probe scheme](deterministic-cell-probe-scheme.md)
- [Randomized cell-probe scheme with private coins](randomized-cell-probe-scheme.md)
- [Word-RAM implementation certificate with potential-amortized running time](../data-structure-interfaces-and-refinement/word-ram-implementation-certificate.md)

## Proof depends on

- [The cell-probe model](../range-query-structures/advanced-data-structures/the-cell-probe-model.md)

## Sources

- P. B. Miltersen, "Cell Probe Complexity - a Survey", Advances in Data Structures Workshop (FSTTCS pre-conference workshop), 1999.
- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 1842-1862, 2023; arXiv:2306.02253.
