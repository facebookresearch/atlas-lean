# Minimum Eulerian cover of a de Bruijn multigraph by local Eulerization

**Setting.** For a $k$-mer multiset $\mathbb M$, the de Bruijn multigraph $dBG(\mathbb M)=(V,E)$ has as vertices the $(k-1)$-prefixes and $(k-1)$-suffixes of the $k$-mers and one arc from prefix to suffix for each occurrence of each $k$-mer. An *Eulerian cover* is a set of trails using every arc exactly once; the readout of a trail $u_1\to\cdots\to u_t$ is $u_1$ followed by the last letters of $u_2,\ldots,u_t$, so an Eulerian cover spells a text representation of $\mathbb M$ with one word per trail. A directed multigraph is *local Eulerian* if each of its weakly connected components has an Eulerian circuit.

**Theorem (local Eulerian criterion).** A directed multigraph is local Eulerian if and only if it is balanced: $d^-(v)=d^+(v)$ for every vertex $v$.

**Lemma (optimal local Eulerization).** Let $\delta(v)=d^-(v)-d^+(v)$. Adding $\sum_v\max(\delta(v),0)$ new arcs, each directed from a vertex with an excess of incoming arcs to a vertex with an excess of outgoing arcs (each vertex used $|\delta(v)|$ times), yields a balanced, hence local Eulerian, multigraph, and no smaller set of added arcs does so.

**Cover construction.** Traverse each component of the Eulerized multigraph by Hierholzer's algorithm and cut the resulting circuits at the added arcs, which are never spelled. Each added arc ends one trail, so every component containing added arcs yields as many words as it has added arcs, and each balanced component yields a single word from its Eulerian circuit. The spelled words form a text representation of $\mathbb M$ that preserves all multiplicities exactly; together with the minimum-word criterion this gives a minimum-weight lossless representation. All steps, and the subsequent Burrows-Wheeler transform with run-length encoding of the concatenated words, run in time and space linear in the input size.

## Depends on

- [Weight of a text representation of a k-mer multiset and the minimum-word criterion](weight-of-a-text-representation-of-a-k-mer-multiset.md)
- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)
- [Every Eulerian trail spells a string with the same k-mer multiset](../../de-bruijn-graph-genome-assembly/kmers-spell-perm.md)

## Expansion

Every arc added at a vertex changes its imbalance by one, so at least $\sum_v\max(\delta(v),0)$ arcs are needed, and pairing in-excess with out-excess units attains this. Cutting an Eulerian circuit of the balanced multigraph at the added arcs splits it into trails of original arcs whose number equals the number of added arcs (or one, if none were added), and conversely any trail cover of a component can be closed into a circuit by joining each trail's end to the next trail's start, so the construction is optimal component by component. Unlike unitig-based or lossy string covers, the representation reproduces the full multiset, including $k$-mer frequencies; in benchmarks it trades compression ratio (near $1$ on noisy data, against about $14$ for a lossy greedy cover) for exact fidelity. As printed, the pseudocode of the source writes the added arc as $(s^-_i,s^+_i)$ with $s^+$ listing vertices of positive $\delta$; balancing requires each added arc to leave a vertex with $\delta>0$ and enter one with $\delta<0$, which is the orientation stated above.

## Sources

- Herman Z. Q. Chen, Sergey Kitaev, Xiaoyu Lang, Artem Pyatkin, Runbin Tang, "Efficient $k$-mer dataset compression using Eulerian covers of de Bruijn graphs and BWT", RAIRO - Theoretical Informatics and Applications 59 (2025), 20, <https://doi.org/10.1051/ita/2025020>. Published version of arXiv:2510.22404, cited next; locators there refer to the arXiv version.
- H. Z. Q. Chen, S. Kitaev, X. Lang and A. Pyatkin, "Efficient k-mer Dataset Compression Using Eulerian Covers of de Bruijn Graphs and BWT", arXiv:2510.22404 (2025), Section "Preliminaries" (Theorems 1 and 2), Section "Algorithm for Minimum Compressed Text Representation" (Lemma 1, local Eulerization and Eulerian cover generation algorithms, complexity analysis), <https://doi.org/10.48550/arXiv.2510.22404>.
