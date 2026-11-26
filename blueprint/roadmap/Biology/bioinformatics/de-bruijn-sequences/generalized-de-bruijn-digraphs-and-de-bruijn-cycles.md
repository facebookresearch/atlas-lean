# Generalized de Bruijn digraphs and their Hamiltonian (de Bruijn) cycles

**De Bruijn digraph.** Over the alphabet $\{0,1,\ldots,d-1\}$, the de Bruijn digraph of order $k$ has the $d^k$ words $(x_1,\ldots,x_k)$ as vertices and an arc $(a_1,\ldots,a_k)\to(b_1,\ldots,b_k)$ whenever $b_i=a_{i+1}$ for $i=1,\ldots,k-1$. Reading vertices as base-$d$ integers, the arcs are the pairs $x\to y$ with $y \equiv dx+r \pmod{d^k}$, $r\in\{0,\ldots,d-1\}$. A *de Bruijn sequence* (or cycle) of order $k$ is a circular word in which every length-$k$ word occurs exactly once; equivalently, a Hamiltonian cycle of this digraph.

**Generalized de Bruijn digraph.** For integers $N>d\ge 2$, $G_B(N,d)$ has vertex set $\{0,1,\ldots,N-1\}$ and arcs $x\to y$ whenever $y\equiv dx+r\pmod N$ for some $r\in\{0,\ldots,d-1\}$; for $N=d^k$ it is the ordinary de Bruijn digraph. Its Hamiltonian cycles are again called de Bruijn cycles.

**Facts.**

1. $G_B(N,d)$ is $d$-regular: every vertex has $d$ successors and $d$ predecessors.
2. If $d\mid N$, the predecessors of $y$ are $\lfloor y/d\rfloor + tN/d$ for $t=0,\ldots,d-1$.
3. If $d\mid N$ and $y_1,y_2$ are successors of $x_1$ and $y_1$ is also a successor of some $x_2\neq x_1$, then $y_2$ is a successor of $x_2$. Vertices with a common pair of successors are called *conjugate*.
4. (Known results quoted in the source.) $G_B(N,d)$ is strongly connected with small diameter, and it is Hamiltonian except when $d=2$ and $N$ is odd.

**Cross-join operation.** Exchanging the successors of two conjugate vertices on a de Bruijn cycle splits it into two cycles; exchanging the successors of a second conjugate pair, one vertex on each cycle, rejoins them into a new de Bruijn cycle. For example, in the binary order-3 cycle $0001110100$, swapping the successors of $110$ and $010$ gives the cycles $00011100$ and $0101$, and then swapping the successors of $001$ and $101$ gives the de Bruijn cycle $0001011100$.

## Depends on

- [De Bruijn multigraph of a string](../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)

## Expansion

When $d\mid N$, the successor sets of $G_B(N,d)$ partition into blocks of $d$ consecutive residues, and each block is the common successor set of exactly $d$ conjugate vertices; this is the structure the cross-join operation exploits. In the ordinary binary case each word $(x_1,x_2,\ldots,x_k)$ has exactly one conjugate, $(\bar x_1,x_2,\ldots,x_k)$. Generalized de Bruijn digraphs drop the restriction that the number of vertices be a power of the alphabet size, which matters when such sequences are used as universal probe or barcode designs of arbitrary length. Cross-join connectivity is developed in the cross-join graph.

## Sources

- Abbas Alhakim, "Hamiltonicity of the Cross-Join Graph of de Bruijn Sequences", arXiv:1805.12059 (2018), Section 2 (cross-join method), Section 3 (Definitions 3.1-3.2, Lemmas 3.3-3.5), Section 4 (Definition 4.1, Lemma 4.2, Theorem 4.3), Section 5 (Algorithm H and its proof of correctness), <https://doi.org/10.48550/arXiv.1805.12059>.
