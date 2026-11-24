# Reduction of CRCW simulation to EREW sorting

In a priority CRCW PRAM, concurrent reads of one memory cell are allowed, and among concurrent writes to one cell the processor with the lowest index succeeds. An EREW PRAM forbids concurrent access to a cell.

**Theorem.** Let $p \ge 2$, and suppose $p$ keys can be sorted on a $p$-processor EREW PRAM in $T_{\mathrm{sort}}(p)$ steps. Then one step of a $p$-processor priority CRCW PRAM can be simulated on a $p$-processor EREW PRAM with $O(p)$ auxiliary cells in $O(T_{\mathrm{sort}}(p) + \log p)$ steps.

**Simulation.** A CRCW step consists of a read phase followed by a write phase. Each phase is simulated separately by the following steps, reads first, so that a cell read and written in the same step returns its old value.
1. Each processor writes its request, the address and its own index, into its own cell of an auxiliary array.
2. The requests are sorted by address, ties broken by processor index.
3. Each position compares its address with that of its left neighbor, in $O(1)$ exclusive steps (each position first copies its address into a second array and then reads its left neighbor's copy), to mark the first request for each address. That request belongs to the lowest-index processor accessing the cell.
4. The processors at marked positions perform the single access to their cells: one read in the read phase, the winning write in the write phase.
5. Read values are broadcast to the remaining requests of each run of equal addresses by recursive doubling in $O(\log p)$ steps.
6. The results are returned to the requesting processors by indexing on processor number.

Every step accesses each cell at most once.

## Sources

- B. Parhami, *Introduction to Parallel Processing: Algorithms and Architectures*, Plenum Press, 1999, Chapter 5 (book not opened; checked against the author's lecture slides for its Part II, "Extreme Models", Fall 2008): the CRCW submodels including priority, and Theorem 5.1 with its justification by sorting the addresses, removing duplicates, accessing memory, and broadcasting by recursive doubling (Fig. 5.2). The steps above make the general sorting bound explicit.
- J. JáJá, *An Introduction to Parallel Algorithms*, Addison-Wesley, 1992 (not opened).
