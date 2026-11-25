# Coalescence records encode a sequence of local trees exactly

Let $n\ge1$ and $0=x_0<x_1<\cdots<x_K=L$, with $K\ge1$, partition $[0,L)$ into intervals $I_k=[x_{k-1},x_k)$. Fix a finite universe $V$ of positive integer node labels containing the samples $S=\{1,\dots,n\}$. On each interval let there be a finite rooted tree with active vertex set $V_k\subseteq V$ and leaf set exactly $S$. Internal nodes may occur in some trees and not others; shared labels mean shared node identity. Encode the tree by a total parent vector $\pi_k:V\to V\cup\{0\}$, with $0$ at its root and at inactive nodes. The sentinel $0$ is not a node. For each active parent $w$ with children, write $C_k(w)=\{u:\pi_k(u)=w\}$ for its full, nonempty child set.

For each signature $(w,C)$ and each maximal consecutive run $I_j,\dots,I_b$ on which $C_k(w)=C$, store one record $(x_{j-1},x_b,w,C)$. Then:

1. **Round trip.** At any $x\in I_k$, initialize all parent entries to zero and, for every record $(\ell,r,w,C)$ with $\ell\le x<r$, set $\pi(u)=w$ for $u\in C$. The result is exactly $\pi_k$. Its active set is recovered as the union of $S$, the nonzero-entry indices, and the nonzero values of $\pi_k$; in particular inactive zero entries are not mistaken for roots.
2. **Sweep.** At a boundary $x_k$, first remove all records ending there (clear the parent entries of their children), then insert all records starting there. After both batches the parent vector is exactly that of $I_{k+1}$. No tree invariant is required of the temporary, partially updated vector. Records use half-open intervals, so the outgoing records do not apply at the boundary itself.
3. **Sharing and size.** The record count is the number of maximal runs of full parent-child-set signatures, not the number of globally distinct parent-child pairs. An assignment shared by adjacent trees uses one record across their boundary, even if the subtree below a child changes. Identical adjacent trees share every record. A signature that disappears and later returns needs separate records. For nonbinary trees, storage must also account for the child entries within each record; record count alone is not a byte-space bound.
4. **Times.** If the input also supplies a shared node-time map $\tau:V\to\mathbb R$ with parent times greater than child times, retain it (or put $\tau(w)$ in each parent record and retain sample times). The same decoding recovers all active node times and every branch length $\tau(\pi_k(u))-\tau(u)$ for nonroot active $u$. Omitting times asserts only topological exactness.

## Proof and examples

Every nonroot active node has one parent in a tree. Its parent's full child set therefore has exactly one maximal-run record covering $I_k$, and that record writes its correct parent. Every active record comes from the input tree and writes no other assignments. Roots and inactive nodes are never children and retain zero. Every active nonsample vertex has a child, so it is a nonzero parent value; together with the known samples this also recovers the active set. Removing all outgoing records before inserting incoming ones preserves precisely the assignments for the next interval, proving the sweep by induction. Times are attached to the same node identities and are therefore recovered along with the parent vector.

For a two-tree example take samples $1,2,3$, universe $\{1,\dots,5\}$ and intervals $[0,1),[1,2)$. The vectors

$$\pi_1=(4,4,5,5,0),\qquad \pi_2=(4,5,4,5,0)$$

encode the first tree by records $(0,1,4,\{1,2\})$, $(0,1,5,\{3,4\})$, and the second by $(1,2,4,\{1,3\})$, $(1,2,5,\{2,4\})$. Decoding recovers both vectors. Inserting before removing would erase incoming assignments to children appearing in both batches, so the order is essential. For $\pi_1,\pi_1$ the two records instead both span $[0,2)$. For $\pi_1,\pi_2,\pi_1$ there are six records, not four distinct signatures. A single-sample tree with no internal nodes needs no records; its known sample is the root. On an empty genome there are no interval queries and the record list is empty.

An **edge-table variant** stores $(\ell,r,w,u)$ for each maximal run of the individual assignment $\pi_k(u)=w\ne0$. It has the same round-trip and remove-before-insert proof, and its row count is the number of maximal parent-child runs. It is not the same row count as grouped coalescence records: in the two-tree example it has six rows (the edges $4\to1$ and $5\to4$ span both intervals), while the grouped encoding has four. With three intervals $\pi_1,\pi_2,\pi_1$, it has eight rows although only six parent-child pairs occur. Thus an encoding-size claim in terms of "distinct edges" must include their genomic extents and fix which encoding is counted.

The result concerns local trees, not reconstruction of the whole ancestral recombination graph: events leaving no trace in the local genealogies cannot be recovered. Supplying the interval trees from a particular ancestral-material process is a separate model application, not an assumption that decoding reconstructs that process.

## Related topics

- [States of the two-locus ancestral process](two-locus-state.md)

## Sources

- J. Kelleher, A. M. Etheridge and G. McVean, "Efficient coalescent simulation and genealogical analysis for large sample sizes", PLoS Computational Biology 12(5) (2016), e1004842, <https://doi.org/10.1371/journal.pcbi.1004842>, sections "Hudson's algorithm with sparse trees", "Tree sequences" and "Generating trees", especially the shared assignments in Figure 4 and Algorithm T. The parent-map round trip and the precise maximal-run counts above are derived directly from the encoding.
