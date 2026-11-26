# Alignment-free homology mapping

Whole-genome homology maps and split-read mappings can be computed without full alignment by estimating, from sampled k-mers, which substrings of a query align to a reference at a given identity. Splitting the query into fragments gives a provable sensitivity bound for detecting every long local alignment, and a plane-sweep filter keeps exactly the mappings that are not dominated by higher-scoring ones along the query.

- [Fragment-seeding sensitivity for long local alignments](fragment-seeding-sensitivity-for-long-local-alignments.md)
- [Plane-sweep filtering of dominated alignment segments](plane-sweep-filtering-of-dominated-alignment-segments.md)
