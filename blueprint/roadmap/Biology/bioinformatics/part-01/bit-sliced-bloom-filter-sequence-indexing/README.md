# Bit-sliced Bloom filter sequence indexing

A collection of sequencing datasets can be searched for a query sequence by storing one Bloom filter of $k$-mers per dataset and transposing the filters into a bit matrix, so that each hash value retrieves a row (a "bit slice") across all datasets and a query reduces to bitwise AND operations.

- [False discoveries of a bit-sliced Bloom filter index](false-discoveries-of-a-bit-sliced-bloom-filter-index.md)
