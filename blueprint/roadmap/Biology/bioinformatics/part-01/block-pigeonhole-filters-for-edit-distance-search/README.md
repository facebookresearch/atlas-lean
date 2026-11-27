# Block pigeonhole filters for edit-distance search

All-pairs similarity search over short reads (for clustering, error correction, or approximate overlaps in assembly) asks for every pair of equal-length strings within edit distance $d$. Seed-and-verify methods rely on a filter that every true neighbour pair must pass; splitting a string into more blocks than allowed errors guarantees a chain of exactly matching blocks at bounded offsets, which can be enumerated by pattern growth and then verified by banded dynamic programming.

- [Block-chain lemma for edit-distance neighbours](block-chain-lemma-for-edit-distance-neighbours.md)
