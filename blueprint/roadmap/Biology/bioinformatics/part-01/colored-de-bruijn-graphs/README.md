# Colored de Bruijn graphs

A colored de Bruijn graph stores the $k$-mers of many sequence data sets in one graph and records, for each edge, the set of data sets (colours) in which it occurs, which supports variant calling and pan-genome queries across samples. Succinct representations based on a Burrows–Wheeler-like ordering of edges make the graph compact, and two such graphs can be merged directly in time linear in the number of edges rather than rebuilt from scratch.

- [Succinct de Bruijn graph and colored-graph merging](succinct-de-bruijn-graph-and-colored-graph-merging.md)
