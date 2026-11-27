# Compressed de Bruijn graph of a pan-genome from an FM-index

**Setting.** Let $S$ be a string of length $n$ over an alphabet of size $\sigma$, typically the
concatenation of several genomes separated by a symbol $\#$ (each occurrence treated as distinct) and
ended by a unique end sentinel. The **de Bruijn graph of order $k$ of $S$** has a node per distinct $k$-mer of $S$
and an edge $(u, v)$ whenever $u = S[i..i+k-1]$ and $v = S[i+1..i+k]$ for some $i$: edges record
consecutive occurrence in $S$, not mere $(k-1)$-overlap. The **compressed de Bruijn graph** merges every
non-branching chain into one node labeled by a longer substring $\omega$; nodes occurring once are
unique nodes, the others repeat nodes (shared segments or repeats).

**Lemma (branching).** Let $v$ be a node other than the start node with string $\omega$. Then $v$ has at
least two distinct predecessors if and only if the length-$k$ prefix of $\omega$ is a **left-maximal
repeat** (occurs at least twice, preceded by at least two distinct characters), and at least two
distinct successors if and only if the length-$k$ suffix of $\omega$ is a **right-maximal repeat**.

**Implicit representation.** Store node $id$ as $(\mathit{len}, \mathit{lb}, \mathit{size},
\mathit{suffix\_lb})$: $[\mathit{lb}..\mathit{lb} + \mathit{size} - 1]$ is the suffix-array interval of $\omega$,
so its occurrence list is $\{\mathrm{SA}[i] : \mathit{lb} \le i < \mathit{lb} + \mathit{size}\}$, and
$\mathit{suffix\_lb}$ starts the interval of the length-$k$ suffix of $\omega$. A bit vector $B_r$ marks the
boundaries of the suffix-array intervals of right-maximal $k$-mers; an interval $[i..j]$ is not inside
any such interval if and only if $\mathrm{rank}_1(B_r, i)$ is even and $B_r[i] = 0$.

**Theorem.** From the wavelet tree of the Burrows-Wheeler transform of $S$ (an FM-index), the implicit
compressed de Bruijn graph is constructed in $O(n \log \sigma)$ time, the explicit graph (with
adjacency lists spelling $S$) in additional $O(N \log \sigma)$ time for $N$ edges, and the FM-index plus
implicit graph support searching a pattern and then traversing the graph from the nodes it hits.

## Depends on

- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)
- [FM-index backward search](../../../../ComputerScience/string-algorithms/burrows-wheeler-transform-and-fm-index/backward-search.md)

## Expansion

A chain stops exactly where some $k$-mer can be entered or left in more than one way, which is the
definition of left- or right-maximality of that $k$-mer; this is the content of the lemma. The
construction starts from each right-maximal $k$-mer (found from the longest-common-prefix array
computed on the FM-index) and extends nodes leftward by backward search steps, each $O(\log \sigma)$ on
the wavelet tree, stopping when the extended prefix becomes a right-maximal $k$-mer or the string
becomes left-maximal. An amortized count shows at most $2n$ intervals are generated, giving the time
bound. Because node identities are suffix-array intervals, locating an allele by backward search
immediately yields its graph node and neighborhood, which the explicit graph alone cannot provide.

## Sources

- T. Beller, E. Ohlebusch, "A representation of a compressed de Bruijn graph for pan-genome analysis
  that enables search", Algorithms for Molecular Biology 11 (2016), Lemmas 1-4 and Algorithms 1-4,
  <https://doi.org/10.1186/s13015-016-0083-7> (PMC4950428).
