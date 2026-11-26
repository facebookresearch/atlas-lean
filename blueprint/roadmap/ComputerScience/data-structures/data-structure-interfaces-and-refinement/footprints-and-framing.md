# Footprints and framing of data structures sharing one memory

For a data structure implemented over a word-addressed memory, its *footprint* in a state is the set of cells its representation depends on, and its *room* is an upper bound on the number of fresh cells its future operations may still allocate. The structure is *framed* if every operation reads and writes only cells of its current footprint and newly allocated cells, and leaves every other cell unchanged. Two framed structures with disjoint footprints, whose combined allocation frontier plus total room fits in an address word, can be run in one shared memory: each operation of one preserves the representation of the other.

## Depends on

- [Refinement of a data-structure specification by an abstraction function](refinement-by-abstraction-function.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- D. E. Knuth, "The Art of Computer Programming, Volume 1: Fundamental Algorithms", 3rd edition, Addison-Wesley, 1997.
