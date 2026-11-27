# Extending a de Bruijn sequence to a larger alphabet with evenly spread new symbols

**Setting.** A de Bruijn sequence of order $n$ over a $k$-symbol alphabet is a circular word of length $k^n$ in which every length-$n$ word occurs exactly once; equivalently, an Eulerian cycle in the de Bruijn graph $G(k,n-1)$, or a Hamiltonian cycle in $G(k,n)$, where $G(k,n)$ has the $k^n$ words of length $n$ as vertices and $k^{n+1}$ edges. A *subsequence* of a circular word is obtained by deleting symbols (not necessarily contiguous ones).

**Theorem.** For every de Bruijn sequence $v$ of order $n$ over a $k$-symbol alphabet there is a de Bruijn sequence $w$ of the same order $n$ over the alphabet enlarged by one new symbol such that $v$ is a subsequence of $w$ and every $n+2k-1$ consecutive symbols of $w$ contain at least one occurrence of the new symbol. Equivalently, between two successive occurrences of the new symbol there are at most $n+2k-2$ other symbols.

**Complexity.** Such a $w$ can be constructed from $v$ in $O(k^{3n-2})$ arithmetic operations.

**Example.** For the binary order-3 sequence $v=[11000101]$, the ternary order-3 sequence

$$w = [122212111002202000120102101]$$

contains $v$ as a subsequence, and every 6 consecutive symbols of $w$ contain a $2$.

## Expansion

The edge set of a de Bruijn graph partitions into disjoint cycles indexed by the circular words one symbol longer. Words over the enlarged alphabet that contain the new symbol $s$ form, in the *augmenting graph* (word graph restricted to arcs with an endpoint containing $s$), closed cycles called *petals*; a petal for an old vertex $u$ passes through exactly one old vertex, namely $u$, so it can be spliced into an old Eulerian cycle at $u$ without changing the order of the old symbols. A *petals tree*, rooted at the old cycle and ordered by the number of occurrences of $s$, organises all circular words containing $s$ so that every new word is inserted exactly once.

The given $v$ is an Eulerian cycle with $k^n$ edges in the order-$(n-1)$ de Bruijn graph; its head vertices are cut into $k^{n-1}$ consecutive *sections* of $k$ vertices. The *distribution graph*, bipartite between old vertices and sections with an edge when the vertex occurs in the section, is $k$-regular, so it has a perfect matching, computed as a maximum flow with the Edmonds-Karp algorithm. Placing one petal per section at the matched vertex puts consecutive petals at most $2k-1$ edges apart. Inside a petal every $n-1$ consecutive edges include one labelled $s$, and the last arc of a petal for $a_1\cdots a_{n-1}$ is $sa_1\cdots a_{n-2}\to a_1\cdots a_{n-1}$. Together these give an occurrence of $s$ in every $n+2k-1$ consecutive symbols.

## Sources

- Verónica Becher, Lucas Cortés, "Extending de Bruijn sequences to larger alphabets", Information Processing Letters 168 (2021), 106085, <https://doi.org/10.1016/j.ipl.2020.106085>. Published version of arXiv:1907.00056, cited next; locators there refer to the arXiv version.
- Verónica Becher and Lucas Cortés, "Extending de Bruijn sequences to larger alphabets", arXiv:1907.00056 (2019), Section 1 (Theorem 1, Proposition 1), Section 2 (Proposition 2, Definitions 1-6, Lemma 1 and the proofs of Theorem 1 and Proposition 1), <https://doi.org/10.48550/arXiv.1907.00056>.
