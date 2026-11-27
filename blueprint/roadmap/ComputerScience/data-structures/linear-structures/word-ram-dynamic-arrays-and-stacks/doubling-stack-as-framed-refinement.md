# A doubling stack is a framed amortized refinement

A bounded word stack with capacity bound $C$ implemented in a doubling array with a three-cell header (size, capacity, base address) is a framed refinement of the stack specification: its footprint is the header and the current array, which moves into fresh cells on growth, and its room is $4C - 2 \cdot \mathrm{capacity}$, which decreases by exactly $2c$ when capacity $c$ doubles. Every push and pop costs $O(1)$ memory operations amortized, so the structure can share one memory with other framed structures.

## Proof sketch

A push into a full array of capacity $c$ allocates $2c$ cells and copies $c$ items, which a potential proportional to the number of items beyond half capacity pays for. The frame and room bookkeeping follows because all writes go to the header, the current array, or the freshly allocated block.

## Depends on

- [Footprints and framing of data structures sharing one memory](../../data-structure-interfaces-and-refinement/footprints-and-framing.md)
- [Refinement of a data-structure specification by an abstraction function](../../data-structure-interfaces-and-refinement/refinement-by-abstraction-function.md)
- [Doubling arrays on the Word RAM](doubling-arrays-on-the-word-ram.md)

## Proof depends on

- [Composition of amortized refinements adds potentials](../../data-structure-interfaces-and-refinement/composition-of-amortized-refinements.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
