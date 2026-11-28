# Orthogonal range reporting with range trees

Let an input list contain $n$ points with coordinates in a linearly ordered set. A query specifies a closed interval for each of $d \geq 1$ coordinates, in order starting at coordinate zero. Equal keys at either endpoint are included; a reversed interval gives no results. The list represents occurrences, so coincident entries are reported with their input multiplicity. The relative order of the reported points is not prescribed.

**Theorem.** Put $B=10(1+\lceil\log_2 n\rceil)$, taking the height to be zero for $n=0$ and $n=1$. The ordinary static range tree reports exactly the occurrences in the box. Its occupied storage is at most $3nB^{d-1}$, and its charged work is at most $B^d+k$, where $k$ is the number of reported occurrences. In one dimension this gives linear storage and $O(1+\log n+k)$ charged work. For any fixed dimension the bounds are $O(n(1+\log n)^{d-1})$ cells and $O((1+\log n)^d+k)$ charged work, with the same convention at zero.

**Construction and proof.** Order the occurrences by the current coordinate and split each nontrivial positional interval into its floor and ceiling halves. At each node above the final coordinate, attach an index on the remaining coordinates for the occurrences in that node. In the final coordinate, a balanced position tree can report any contained subtree as a slice of one shared sorted array.

Binary searches give the first positions not below the lower endpoint and above the upper endpoint. These delimit a half-open positional interval. Skip a disjoint node, emit a contained node, and descend to both children only at a partial overlap. Such a split contains at least one query boundary strictly in its interior, and at each depth the disjoint intervals contain each boundary at most once. The emitted subtrees therefore cover the query interval exactly and without overlap, with only $O(1+\log n)$ node inspections. Each emitted subtree dispatches one search on its attached index, except at the final coordinate where it emits the selected entries once. This yields one factor of $O(1+\log n)$ per coordinate for search and a separate output charge. For storage, a point belongs to at most one node of a given depth: multiplying by the number of depths at each additional coordinate gives the storage bound.

Reporting threads a single output tail through the selected subtrees. At a split the right subtree fills the tail first, and the left subtree then prepends its output, so the resulting list keeps the order of the canonical nodes. Each terminal iterator reads its selected positions in descending order and prepends each reference exactly once. Neither traversal nor finalization copies a slice, appends an intermediate result list, or scans the output to count it.

A search probe charges an indexed read, a unit-cost coordinate lookup and comparison, and fixed index and control operations. A visit charges endpoint tests, child selection, continuation work and bookkeeping, including the root's fixed boundary-search setup and exit and the terminal iterator's setup and exit where applicable. An emission charges the indexed read, loop and count operations, and one cons. Occupied storage counts static catalog slots and tree records, not the point payloads, coordinate oracle, fixed root descriptors, empty sentinels, or query workspace. These are static query and storage bounds under the stated primitives, not preprocessing, bit-complexity or evaluator-time bounds.

## Background

- [Range tree](range-tree.md)
- [Layered range reporting](layered-range-reporting.md)
- [Fractional cascading](../fractional-cascading/README.md)
- [Orthogonal range reporting in a kd-tree](../k-d-tree/orthogonal-range-reporting-in-a-kd-tree.md)

## Sources

- E. Demaine, *6.851: Advanced Data Structures*, Lecture 3 “Geometric structures” (scribe notes, 23 February 2012), MIT, <https://courses.csail.mit.edu/6.851/spring21/scribe/lec3.pdf>. Section 3.1 describes the balanced leaf tree, the canonical subtrees on the two boundary paths, and the ordinary nested bounds. Section 3.2 uses parent-to-child positions in the final coordinate to remove one logarithmic search factor.
