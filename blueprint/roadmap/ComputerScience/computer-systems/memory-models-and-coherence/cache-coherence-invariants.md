# Cache coherence invariants

The model describes one location at the boundaries of its epochs, each associated with a finite
set of cores. It separates the following conditions:

1. **Single-writer–multiple-reader (SWMR).** If a core may write, it may also read and no other
   core may do either. If no core may write, any number of cores may read, including zero.
2. **Data value.** The logical value of the location at the start of an epoch is the end value of
   the most recent completed read–write epoch. When there is no such epoch, use an explicit
   initial value. Read-only epochs leave the carried value unchanged.

For the token rule, fix a positive number of tokens at least as large as the number of cores.
The counts held by the cores and the unassigned count add to that total. A core holding all tokens
may write; a core holding at least one token may read. If a core may write, every other core's
count is zero, proving SWMR. Without a writer the rule places no value constraint on readable
copies. For example, two cores holding one token each out of two are readers; their copies can
still differ, even if the epoch's logical start value is correct.

If the logical start value is carried forward as in condition 2 and every readable copy matches
that start value, then every reader sees the carried value, so any two readers agree. The
copy-matching condition is separate from token ownership. The model checks these conditions at
epoch boundaries; it does not specify a protocol for transferring tokens, moving values, or
invalidating copies within an epoch.

## Sources

- D. J. Sorin, M. D. Hill and D. A. Wood, *A Primer on Memory Consistency and Cache Coherence*, Synthesis Lectures on Computer Architecture, Morgan & Claypool, 2011, Section 2.3 (the coherence invariants, the epoch picture of Figure 2.3, the token interpretation) and Section 2.3.1 (maintaining the invariants).
- *Cache coherence*, lecture notes for CS 149, Stanford University, 27 October 2022, <https://saligrama.io/notes/cs149/2022-10-27-cache-coherence/>: the single-writer–multiple-reader and data-value invariants.
