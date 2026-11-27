# Linear-time minimum spectrum-preserving string set without repetitions

**Setting.** A $k$-mer is a string of length $k$ identified with its reverse complement. For a set $I$ of strings of length at least $k$ over an alphabet $\Sigma$, let $CS_k(I)$ be its set of (canonical) $k$-mers and $\|I\|$ its cumulative length. A *spectrum-preserving string set* (SPSS) of $I$ is a set $I'$ of strings of length at least $k$ with $CS_k(I') = CS_k(I)$; it is *without repetitions* if each $k$-mer occurs only once in $I'$. In the arc-centric bidirected de Bruijn graph of order $k$, nodes are $(k-1)$-mers and each $k$-mer is an arc; an SPSS without repetitions is exactly the spelling of a unique walk cover, and a cover with $w$ walks spells strings of total length $|CS_k(I)| + w(k-1)$.

**Theorem.** One can compute an SPSS $I'$ of $I$ without repetitions and of minimum cumulative length in $O(\|I\| \log|\Sigma|)$ time. Its strings (*Eulertigs*) are obtained by Eulerizing each connected component of the de Bruijn graph, finding a Eulerian cycle, and breaking it at the inserted arcs; a component $G_i$ contributes $\max\bigl(1, \mathrm{imbalance}(G_i)/2\bigr)$ strings. This gives a tight, easily computed lower bound for repetition-free representations, against which the heuristics UST and ProphAsm turn out to be near-optimal but not always optimal.

## Depends on

- [Minimum walk cover of a bidirected graph by imbalance](minimum-walk-cover-of-a-bidirected-graph-by-imbalance.md)

## Expansion

The compacted arc-centric bidirected de Bruijn graph is built in $O(\|I\| \log |\Sigma|)$ time from a suffix-tree-type index of the input, and has $O(\|I\|)$ nodes and arcs. Since every walk of $w$ walks pays $k-1$ overlap characters, minimizing total length means minimizing $w$, which the imbalance bound settles exactly; spelling the walks takes time linear in the output, which is no larger than the input.

## Sources

- S. Schmidt and J. N. Alanko, "Eulertigs: minimum plain text representation of k-mer sets without repetitions in linear time", *Algorithms for Molecular Biology* (2023), Theorem 1, Theorems 6 and 8 (de Bruijn graph construction) and the section "Computing a minimum SPSS without repetitions". <https://doi.org/10.1186/s13015-023-00227-1> (PMC10318842)
