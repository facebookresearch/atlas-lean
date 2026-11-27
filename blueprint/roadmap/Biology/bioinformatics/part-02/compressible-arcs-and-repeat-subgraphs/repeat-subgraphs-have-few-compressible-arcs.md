# Repeat subgraphs have few compressible arcs

**Definitions.** For reads $R \subseteq \Sigma^*$ and integer $k$, the de Bruijn graph $G_k(R) = (V, A)$ has as vertices the distinct $k$-mers of $R$ and an arc $(u,v)$ whenever $u[2,k] = v[1,k-1]$. An arc $(u,v)$ is **compressible** if $d^+(u) = 1$ and $d^-(v) = 1$, so every path through $u$ continues to $v$. Compressible arcs labelled $s = s_1\cdots s_{k+1}$ correspond one-to-one to **boundary rigid** $(k-1)$-mers $s[2,k]$ of $R$, those always preceded by $s_1$ and followed by $s_{k+1}$.

**Repeat model.** Choose $s_0 \in \Sigma^n$ uniformly; for $i = 1, \dots, m$ create $s_i$ by keeping each position $s_0[j]$ with probability $1 - \alpha$ and otherwise replacing it by a uniformly chosen different letter. The set $S(m,n,\alpha) = \{s_1,\dots,s_m\}$ models $m$ copies of a repeat at expected Hamming distance $\alpha n$ from the ancestor.

**Theorem 1.** For integers $k < n$, $m$ and $0 \le \alpha \le 3/4$, the de Bruijn graph $G_k(S(m,n,\alpha))$ has $o(nm)$ expected compressible arcs.

**Theorem 2.** The **repeat subgraph problem** (given a directed graph and integers $m$, $t$, decide whether there is a connected subgraph with at least $m$ vertices and at most $t$ compressible arcs) is NP-complete, even for directed graphs of total degree bounded by $d$ for any $d \ge 3$.

## Depends on

- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)

## Proof depends on

- [STEINER TREE is NP-complete](../../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/steiner-tree/steiner-tree-np-complete.md)

## Expansion

A $(k-1)$-mer is boundary rigid only if all $m$ copies agree on the letters flanking every one of its occurrences; mutations at independent columns make such agreement increasingly unlikely as $m$ grows, so by linearity of expectation the count of rigid positions is a vanishing fraction of the $m(n-k+2)$ candidates. A repeat therefore looks like a dense tangle with almost no compressible arcs, while a transcript without repeats is a chain of them. Hardness comes from a reduction from Steiner tree with weights 1 and 2: each vertex becomes a degree-3 gadget with no compressible arcs, and each weighted edge a path of one or two compressible arcs, so a large connected subgraph with few compressible arcs is exactly a cheap Steiner tree. In local assembly of alternative-splicing bubbles, restricting the search to bubbles with enough compressible arcs avoids repeat-associated subgraphs without having to identify them.

## Sources

- L. Lima, B. Sinaimeri, G. Sacomoto, H. Lopez-Maestre, C. Marchet, V. Miele, M.-F. Sagot, V. Lacroix, "Playing hide and seek with repeats in local and global de novo transcriptome assembly of short RNA-seq reads", Algorithms for Molecular Biology 12:2 (2017), Definition 1, the repeat model $S(m,n,\alpha)$, Theorems 1–2, <https://doi.org/10.1186/s13015-017-0091-2>, PMCID PMC5322684.
