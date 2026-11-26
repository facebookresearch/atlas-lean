# Cache coherence invariants

Consider a shared-memory system of cores with private caches, and divide the lifetime of each memory location into *epochs*. In each epoch, either a single core has read–write access to the location, or some number of cores, possibly zero, have read-only access. A memory system is *coherent* if it maintains, for every memory location $A$, the following two invariants in logical time:

1. **Single-writer–multiple-reader (SWMR) invariant.** At any given logical time, either a single core may write $A$ (and may also read it), or some number of cores may only read $A$.
2. **Data-value invariant.** The value of $A$ at the start of an epoch equals its value at the end of its last read–write epoch.

The SWMR invariant alone does not suffice: two cores could read different values in the same read-only epoch.

A token formulation of the SWMR invariant gives each location a fixed number of tokens, at least the number of cores. A core holding all the tokens may write the location, and a core holding at least one token may read it. These rules enforce the SWMR invariant only; the data-value invariant needs in addition that data is transferred with the tokens, so that every core holding a token holds the current value.

Invalidate protocols maintain the invariants directly. To read, a core ends any read–write epoch of another core and starts a read-only epoch. To write, it obtains the current value and ends every other core's access, starting a new read–write epoch.

## Sources

- D. J. Sorin, M. D. Hill and D. A. Wood, *A Primer on Memory Consistency and Cache Coherence*, Synthesis Lectures on Computer Architecture, Morgan & Claypool, 2011, Section 2.3 (the coherence invariants, the epoch picture of Figure 2.3, the token interpretation) and Section 2.3.1 (maintaining the invariants).
- *Cache coherence*, lecture notes for CS 149, Stanford University, 27 October 2022, <https://saligrama.io/notes/cs149/2022-10-27-cache-coherence/>: the single-writer–multiple-reader and data-value invariants.
