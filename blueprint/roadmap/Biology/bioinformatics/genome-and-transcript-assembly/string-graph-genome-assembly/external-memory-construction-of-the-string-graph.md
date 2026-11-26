# External-memory construction of the string graph

**Definitions.** Let $R$ be a substring-free set of reads (strings over $\{A,C,G,T\}$) of total length $n$, no read longer than $l$. Two reads $r_i,r_j$ *overlap* if a nonempty suffix $ov_{i,j}$ of $r_i$ equals a prefix of $r_j$; write $r_i=lx_{i,j}\,ov_{i,j}$ and $r_j=ov_{i,j}\,rx_{i,j}$, with left extension $lx_{i,j}$ and right extension $rx_{i,j}$.

- The **overlap graph** $G_O=(R,A)$ has an arc $(r_i,r_j)$ labeled $lx_{i,j}$ for every overlapping pair. The *assembly* of a path $r_{i_1},\dots,r_{i_k}$ is $lx_{i_1,i_2}\cdots lx_{i_{k-1},i_k}\,r_{i_k}$, which equals $r_{i_1}\,rx_{i_1,i_2}\cdots rx_{i_{k-1},i_k}$.
- An arc $(r_i,r_j)$ is **reducible** if another path from $r_i$ to $r_j$ has the same assembly $lx_{i,j}r_j$. Removing all reducible arcs gives the **string graph** $G_S$ (Myers), which has the same set of distinct path assemblies as $G_O$.

**Characterization (Lemma).** An arc $(r_i,r_j)$ of $G_O$ is reducible if and only if there is another arc $(r_h,r_j)$ entering $r_j$ such that the reversed left extension $lx^{\mathrm{rev}}_{h,j}$ is a proper prefix of $lx^{\mathrm{rev}}_{i,j}$.

**Theorem (I/O complexity).** Given the Burrows–Wheeler transform, generalized suffix array and LCP array of $R$ as sequential files:

1. the overlap graph can be computed by reading sequentially $(3+6l)n$ records;
2. the irreducible arcs (that is, the string graph) can then be extracted from $G_O$ while reading or writing at most $3\,|E(G_O)|\,\lceil d/M\rceil$ records, where $d$ is the maximum indegree of $G_S$ and $M$ is the number of records that fit in main memory.

Both stages access disk only by sequential scans, matching the I/O cost of the best external-memory algorithms that build the BWT, suffix array and LCP indexes themselves.

## Expansion

For a string $S$, the reads having $S$ as a suffix and those having $S$ as a prefix form contiguous intervals $q(S\$)$ and $q(\$S)$ of the sorted suffixes, so the set of arcs with overlap $S$ is the product of two BWT intervals. Backward extension $q(\sigma S)=[C(\sigma)+\mathrm{Occ}(\sigma,b)+1,\ C(\sigma)+\mathrm{Occ}(\sigma,e))$ grows candidate overlaps one character at a time, so each of at most $l$ rounds scans the BWT and the current interval lists once. Reduction uses the characterization: arcs entering $r_j$ are processed by increasing length of $lx$, and an arc is transitive exactly when an already-kept arc's reversed label interval contains its own, which is a nested-interval test done with a stack in one pass.

## Sources

- Paola Bonizzoni, Gianluca Della Vedova, Yuri Pirola, Marco Previtali, Raffaella Rizzi, "An External-Memory Algorithm for String Graph Construction", arXiv:1405.7520 (2014), Definition of the overlap and string graphs (Section 2), Proposition 3, Corollary 25, Lemma 26 and Theorem 31, <https://doi.org/10.48550/arXiv.1405.7520>.
