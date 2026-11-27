# Succinct de Bruijn graph and colored-graph merging

**Colored de Bruijn graph.** Fix $k \ge 2$ and an alphabet $\Sigma$. The de Bruijn graph $G = (V, E)$ of a set of sequences has one node per distinct $(k-1)$-mer and one edge per distinct $k$-mer, from its $(k-1)$-prefix to its $(k-1)$-suffix. Given data sets $D_1, \dots, D_t$, the colored de Bruijn graph is the de Bruijn graph of their union together with a $|E| \times t$ binary colour matrix whose entry $(e, c)$ is $1$ iff the $k$-mer of $e$ occurs in $D_c$.

**Succinct (edge-BWT) representation.** Order nodes co-lexicographically, i.e. by the lexicographic order of their reversed $(k-1)$-mers. Let $L$ list the edges sorted by (colex rank of start node, then end node) and $F$ the edges sorted by (colex rank of end node, then start node), and let $\mathrm{label}(e)$ be the last symbol of the $k$-mer of $e$. Then:

- Edges with the same label appear in the same relative order in $L$ and $F$; edges with different labels are ordered in $F$ by label. Hence the edge at position $p$ of $L$ is at position

$$\big|\{ d \in E : \mathrm{label}(d) \prec \mathrm{label}(e) \}\big| + \big|\{ h \le p : \mathrm{label}(L[h]) = \mathrm{label}(e) \}\big| - 1$$

of $F$ (positions from $0$), an LF-mapping computable with rank queries.
- Storing only the label sequence $\mathrm{EdgeBWT}(G) = (\mathrm{label}(L[h]))_h$ and two bit vectors $B_L$, $B_F$ marking the last outgoing (resp. incoming) edge of each node supports forward and backward traversal, and a node's $(k-1)$-mer is recovered by $k-1$ backward steps. Dummy nodes and edges guarantee that every original node has an incoming path of length at least $k-1$.

**Theorem (merging).** Let $G_1 = (V_1, E_1)$ and $G_2 = (V_2, E_2)$ be colored de Bruijn graphs for the same $k$ in this representation, with $|E_1| \ge |E_2|$, and let $t$ be the number of colours of the merged graph. The merged colored de Bruijn graph $G_M$ (whose $k$-mer set is the union and whose colour matrix is the concatenation of colour columns) can be constructed in

$$O\big(|E_1| \cdot \max(k, t)\big)$$

time, without decoding the graphs to $k$-mer lists and re-sorting.

## Expansion

A naive merge reconstructs all $k$-mers of both graphs by backward walks and merges two sorted lists. The direct merge instead plans the merge as lists of intervals of $L_1$ and $L_2$ and refines them over $k$ rounds, a partition of the two edge lists into blocks that agree on the last $i$ symbols of their node labels, using only the symbols exposed one at a time by backward navigation; after these rounds the relative colex order of all nodes of both graphs is known and identical $k$-mers are aligned. Each round is a linear scan, giving the $O(|E_1|\,k)$ term, and copying the two colour matrices row by row into the merged order gives the $O(|E_1|\,t)$ term. Merging makes the structure updatable: new samples are added by building a small graph and merging it into the existing one.

## Sources

- M. D. Muggli, B. Alipanahi, C. Boucher, "Building large updatable colored de Bruijn graphs via merging", Bioinformatics 35 (2019) i51–i60, Section 3 (succinct representation, colex order, LF position formula, $B_F$, $B_L$, dummy edges) and Section 4 (naive and direct merge algorithms, Theorem 1), <https://doi.org/10.1093/bioinformatics/btz350> (PMC6612864).
- A. Bowe, T. Onodera, K. Sadakane, T. Shibuya, "Succinct de Bruijn graphs", Algorithms in Bioinformatics (WABI 2012), Lecture Notes in Computer Science 7534, 225–235, <https://doi.org/10.1007/978-3-642-33122-0_18>.
