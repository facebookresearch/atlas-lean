# Doubly-connected edge list

A *doubly-connected edge list* represents a subdivision of the plane by a planar straight-line graph whose faces have no holes, by three sets of records. Each undirected edge is stored as two oppositely directed *half-edges*; a half-edge $e$ stores its *twin* (the opposite half-edge), its origin vertex $e.\mathrm{org}$ (its destination is $e.\mathrm{twin}.\mathrm{org}$), the face $e.\mathrm{left}$ to its left, and the next and previous half-edges $e.\mathrm{next}$ and $e.\mathrm{prev}$ in counterclockwise order around that face. Each vertex stores its coordinates and one half-edge with origin at it, and each face stores one half-edge that has it on its left. Following $\mathrm{next}$ pointers from that half-edge enumerates the boundary of a face in time proportional to its number of edges.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 10, "Doubly-connected Edge List": vertex, half-edge and face records, under the assumption that faces have no holes
