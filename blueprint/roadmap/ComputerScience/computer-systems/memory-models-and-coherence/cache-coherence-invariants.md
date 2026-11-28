# Cache coherence invariants

Coherence in a shared-memory system requires two invariants for every memory location at every
logical time. For one location, divide its lifetime into an ordered sequence of epochs. A finite
history is coherent when every epoch satisfies both conditions below:

1. **Single-writer–multiple-reader (SWMR).** If a core may write, it may also read and no other
   core may do either. If no core may write, any number of cores may read, including zero.
2. **Data value.** The location starts each epoch with the end value of the most recent completed
   read–write epoch, or with the given initial value if there was none. Read-only epochs leave the
   carried value unchanged. Every readable copy at the start of the epoch equals that epoch's
   logical start value, which exists even when no core may read.

SWMR alone does not imply data-value agreement: two cores may have different copies in the same
read-only epoch. In a token formulation, fix a positive number of tokens for the location, at
least as large as the number of cores. The counts held by cores and the unassigned count add to
that total. Holding all tokens grants write access, and holding at least one grants read access.
If one core holds them all, every other core holds zero, so the permissions obey SWMR. The
permissions do not determine the contents of the copies. The data associated with the tokens
must remain consistent with the value carried through the epoch boundaries.

These conditions concern the history of snapshots for one location. They do not specify how
permissions and values change during an epoch or require a particular protocol.

## Sources

- D. J. Sorin, M. D. Hill and D. A. Wood, *A Primer on Memory Consistency and Cache Coherence*, Synthesis Lectures on Computer Architecture, Morgan & Claypool, 2011, Section 2.3 (the coherence invariants, the epoch picture of Figure 2.3, and the token interpretation).
- *Cache coherence*, lecture notes for CS 149, Stanford University, 27 October 2022, <https://saligrama.io/notes/cs149/2022-10-27-cache-coherence/>: the single-writer–multiple-reader and data-value invariants.
