# Safe sequences for path covers of DAGs via dominator trees

**Setting.** In RNA transcript assembly, a splice graph is an $s$-$t$ DAG $G = (N,A)$ with $n$ nodes and $m$ arcs, and transcripts are recovered as a set of $s$-$t$ paths that covers the graph and best explains arc weights (read abundances). A **path cover** is a set of $s$-$t$ paths covering every node. A sequence $X$ of nodes is **safe** if, in every path cover, some path contains $X$ as a (not necessarily contiguous) subsequence; it is **maximal** if it is not a proper subsequence of another safe sequence. A $u$-$v$ **cutnode** is a node lying on every $u$-$v$ path. In the $s$-dominator tree, the ancestors of $v$ are exactly the $s$-$v$ cutnodes; the $t$-dominator tree records $v$-$t$ cutnodes in the same way. For a node $u$, let $\mathrm{extension}(u)$ be the concatenation of the $s$-$u$ cutnodes and the $u$-$t$ cutnodes.

**Theorem (characterization).** For a sequence $X$ of nodes in an $s$-$t$ DAG, the following are equivalent:
1. $X$ is safe for path covers;
2. some node $u$ has the property that every $s$-$t$ path through $u$ contains $X$;
3. some node $v$ has $X$ contained in the concatenation of the sequences of $s$-$v$ and $v$-$t$ cutnodes.

**Theorem (maximal safe sequences).** In a compressed $s$-$t$ DAG (unitary arcs $uv$ with $N^+_u = \{v\}$, $N^-_v = \{u\}$ contracted, computable in $O(n+m)$ time), $\mathrm{extension}(u)$ is a maximal safe sequence iff $u$ is a leaf in **both** the $s$-dominator tree and the $t$-dominator tree. Consequently the maximal safe sequences have an $O(n)$-size representation by leaf-to-root paths of the two dominator trees, buildable in $O(n+m)$ time, and they can be enumerated without duplicates in output-sensitive optimal time $O(m + o)$, where $o$ is their total length. Analogous enumeration results (output-optimal enumeration and a linear-size representation of the maximal safe sequences) hold for covers of a given subset of nodes and for covers of the arcs (ESA 2025, after Theorem 3).

**Application.** Every maximal safe sequence must appear in some solution path of any arc-covering or node-covering transcript model. Fixing the corresponding path variables simplifies the integer linear programs for least-squares path decomposition (minimize $\sum_{uv}\big(w(uv) - \sum_{i: uv\in P_i}w_i\big)^2$ over $k$ weighted paths) and for robust path decomposition with per-path slacks. On wide graphs this gives average speed-ups of about $50$–$350\times$, while the safe sequences themselves take under $0.1$ s per graph on average.

## Expansion

If every path through $u$ contains $X$, then any path cover, which must cover $u$, contains such a path, so $X$ is safe. Every $s$-$t$ path through $v$ passes through all $s$-$v$ and $v$-$t$ cutnodes in order, which gives the third form. Maximality corresponds to choosing $v$ as deep as possible in both dominator trees at once; compression removes the ambiguity caused by unitary paths, along which all nodes have the same extension.

## Sources

- Francisco Sena, Romeo Rizzi and Alexandru I. Tomescu, "Safe Sequences via Dominators in DAGs for Path-Covering Problems", ESA 2025, LIPIcs 351, paper 55 (remark after Theorem 3 on subset and arc covers); preprint arXiv:2411.03871 (2024), Section 1 (Theorem 1, characterization of safe sequences; Theorems 2–3, computation and enumeration of maximal safe sequences), Section 3.3 (Theorem 4, characterization of maximal safe sequences), Theorems 5–8 (subset and arc covers), numbering of v3–v4, Section 4 (experiments), Appendices A, B and D, <https://doi.org/10.48550/arXiv.2411.03871>.
