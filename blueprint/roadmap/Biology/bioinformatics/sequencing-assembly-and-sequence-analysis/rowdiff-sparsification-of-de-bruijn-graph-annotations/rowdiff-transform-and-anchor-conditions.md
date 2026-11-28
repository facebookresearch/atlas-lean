# RowDiff transform and its anchor conditions

**Setting.** Let $G_k = (V_k, E_k)$ be the vertex-centric de Bruijn graph of order $k$ of a sequence collection (vertices are $k$-mers, with an arc $(u, v)$ when the $(k-1)$-suffix of $u$ equals the $(k-1)$-prefix of $v$), and let $A \in \{0, 1\}^{|V_k| \times |L|}$ be a binary annotation matrix whose row $A_u$ marks the labels (samples, genomes) containing $k$-mer $u$. For each non-sink vertex $u$, its **RowDiff successor** $\mathrm{succ}(u)$ is its lexicographically largest out-neighbour. Given an anchor vector $a \in \{0, 1\}^{|V_k|}$, the **RowDiff transform** replaces $A$ by $A^*$ with

$$A_u^* = \begin{cases} A_u, & a_u = 1 \text{ (anchor)}, \\ A_u \oplus A_{\mathrm{succ}(u)}, & a_u = 0, \end{cases}$$

where $\oplus$ is element-wise XOR. The inverse (Algorithm 1) reconstructs $A_u$ by following $u, \mathrm{succ}(u), \mathrm{succ}^2(u), \dots$ until the first anchor $w$ and XOR-ing the transformed rows along the path: $A_u = A_u^* \oplus A^*_{\mathrm{succ}(u)} \oplus \cdots \oplus A_w^*$.

A **RowDiff cycle** is a directed cycle $u_1 \to u_2 \to \cdots \to u_r \to u_1$ with $u_{i+1} = \mathrm{succ}(u_i)$.

**Proposition 1.** Algorithm 1 terminates from every starting vertex if and only if every sink vertex is an anchor and every RowDiff cycle contains at least one anchor.

**Proposition 2.** Whenever it terminates, Algorithm 1 returns the original row $A_i$ for every $i \in V_k$.

**Proposition 4 (anchor optimization).** If, in addition, every vertex $v$ with $\mathrm{popcount}(A_v^*) > \mathrm{popcount}(A_v)$ is made an anchor, then every row of $A^*$ has at most as many set bits as the corresponding row of $A$, so the transform never densifies a row.

## Depends on

- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)

## Expansion

The successor map $\mathrm{succ}$ is a partial function, so its functional graph consists of paths into sinks and of cycles with in-trees; following it from any vertex either reaches a sink, enters a cycle, or meets an anchor. Hence termination requires exactly anchors at sinks and on every cycle. Correctness is the telescoping identity $A_u = A_u^* \oplus A_{\mathrm{succ}(u)}$ for non-anchors, applied along the path. Turning a vertex into an anchor never breaks the other conditions, which is why the density-reducing anchor optimization is free. The paper constructs anchors in linear time with a forward traversal (Algorithm 2, Proposition 3) and additionally bounds path lengths to anchors with a heuristic, which controls query time; empirically the sparsified matrix compresses by large factors when neighbouring $k$-mers share labels.

## Sources

- D. Danciu, M. Karasikov, H. Mustafa, A. Kahles, G. Rätsch, "Topology-based sparsification of graph annotations", Bioinformatics 37 (Supplement 1) (2021) i169–i176, Sections 2.2–2.3.1, Algorithms 1–2, Propositions 1–4, <https://doi.org/10.1093/bioinformatics/btab330> (PMC8346655).
