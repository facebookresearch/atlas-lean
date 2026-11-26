# Junction positions determine the compacted de Bruijn graph

**Setting.** For a string $s$ and integer $k$, the de Bruijn graph $G(s,k)$ has the $k$-mers of $s$ as vertices and an edge $u\to v$ whenever some $(k+1)$-mer of $s$ has prefix $u$ and suffix $v$; for a collection $S=\{s_1,\dots,s_n\}$ of complete genomes, $G(S,k)=\bigcup_iG(s_i,k)$. A vertex is a *bifurcation* if it has more than one incoming or more than one outgoing edge, a *sentinel* if it is the first or last $k$-mer of an input string, and a *junction* if it is either. The *compacted* de Bruijn graph replaces every maximal non-branching path by a single edge.

**Observation (reduction to junctions).** Let $P$ be the set of maximal non-branching paths of $G(s,k)$ and $T$ the set of substrings of $s$ that start and end with a junction $k$-mer and contain no junction in between. Then there is a bijection $g:T\to P$. Hence the compacted graph is determined by the set $J(S,k)$ of string positions at which junction $k$-mers occur.

**Two-pass algorithm and false junctions.** A first pass inserts all $(k+1)$-mers of $S$ into a Bloom filter with $b$ bits and $h$ hash functions and marks a position as a candidate junction if the filter reports more than one in- or out-neighbour; a second pass removes false candidates with an exact hash table. If the graph has $E$ edges and $L$ non-junction vertices, the expected number of false-positive junctions after the first pass is

$$
\mathbb E[\mathrm{FP}]=L\Big(1-(1-q)^6\Big),\qquad q=\big(1-e^{-hE/b}\big)^h,
$$

assuming independent queries, since each non-junction vertex has one true in-edge and one true out-edge and three possible false edges on each side.

## Expansion

In a de Bruijn graph built from complete strings, every non-junction $k$-mer has exactly one predecessor and one successor, and consecutive $k$-mers of the input are joined by edges; so a maximal non-branching path is exactly a run of consecutive positions between two junction occurrences, giving the bijection. Detecting junctions needs only neighbourhood queries, which a Bloom filter answers with one-sided error: true junctions are never missed, and false positives are filtered in the second pass, whose memory is proportional to the surviving candidates rather than to all $k$-mers. Both passes stream the input with rolling hashes in $O(mh)$ time for total input length $m$, and the input can be split into rounds when memory is limited, which makes compacted graphs of many complete mammalian genomes feasible.

## Depends on

- [The k-mers of a string](../../de-bruijn-graph-genome-assembly/kmers.md)
- [Exponential approximation of the Bloom filter false-positive rate](../../../../ComputerScience/data-structures/hashing/bloom-filter/exp-approx.md)

## Sources

- Ilia Minkin, Son Pham, Paul Medvedev, "TwoPaCo: An efficient algorithm to build the compacted de Bruijn graph from many complete genomes", arXiv:1602.05856: Section 2 (preliminaries), Section 3 (Observation 1, reduction to junction positions), Section 4 (single-round two-pass algorithm), Section 7 (theoretical analysis of false-positive junctions and running time). <https://doi.org/10.48550/arXiv.1602.05856>
