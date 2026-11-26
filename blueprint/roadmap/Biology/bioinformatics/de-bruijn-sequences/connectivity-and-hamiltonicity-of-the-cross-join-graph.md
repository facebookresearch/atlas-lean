# Connectivity and Hamiltonicity of the cross-join graph of de Bruijn cycles

**Cross-join graph.** For a generalized de Bruijn digraph $G_B(N,d)$ (vertices $\{0,\ldots,N-1\}$, arcs $x\to dx+r \bmod N$), let $\mathcal C(N,d)$ be the graph whose vertices are all de Bruijn (Hamiltonian) cycles of $G_B(N,d)$, two cycles being adjacent when one is obtained from the other by a single cross-join operation (two successor exchanges between conjugate vertices). Fix all cycles to start at vertex $0$ and, for two cycles $u,v$, let

$$\mathcal D(u,v) = N - L,$$

where $L$ is the length of the longest common initial path of $u$ and $v$.

**Lemma (distance reduction).** If $d\mid N$ and $u\neq v$ are de Bruijn cycles of $G_B(N,d)$, there is a cross-join neighbour $u_1$ of $u$ with $\mathcal D(u_1,v)<\mathcal D(u,v)$; moreover $u_1$ keeps the common initial path of $u$ and $v$.

**Theorem.** If $d\mid N$, the cross-join graph $\mathcal C(N,d)$ is connected. In particular, for $N=d^k$, any de Bruijn sequence of order $k$ over a $d$-letter alphabet can be transformed into any other by repeated cross-joins, extending the binary result of Mykkeltveit and Szmidt.

**Hamiltonian path (Algorithm H).** Starting from any de Bruijn cycle $u_1$ with $x_1=0$, repeatedly move from the current cycle $u_k$ to the not-yet-output cross-join neighbour that preserves the longest possible initial segment (trying conjugate pairs $(i,i')$, $i<i'$, in decreasing lexicographic order), and halt when no new neighbour exists. The output visits every de Bruijn cycle of $G_B(N,d)$ exactly once, i.e. it is a Hamiltonian path of $\mathcal C(N,d)$, a "de Bruijn sequence of de Bruijn sequences".

## Depends on

- [Generalized de Bruijn digraphs and their Hamiltonian (de Bruijn) cycles](generalized-de-bruijn-digraphs-and-de-bruijn-cycles.md)

## Expansion

*Lemma.* Let the cycles agree on their first $L$ vertices and differ at the next one. Using the successor structure available when $d\mid N$, one finds two conjugate pairs whose successor exchanges redirect $u$ to follow $v$ one step further while leaving the first $L$ vertices untouched; the result is again a single Hamiltonian cycle. *Theorem.* Iterating the lemma strictly decreases $\mathcal D(\cdot,v)$, so a path to $v$ exists.

*Algorithm H.* Suppose a cycle $v$ is never output. Take the last output $u_{k_0}$ sharing the longest initial segment, of length $l$, with $v$. The lemma gives an unvisited neighbour of $u_{k_0}$ keeping that segment and agreeing with $v$ beyond it, so $u_{k_0}$ is not the last output. If the next output $u_{k_0+1}$ keeps at least $l$ initial vertices, it contradicts the maximality of $k_0$; otherwise the algorithm skipped a neighbour preserving a longer segment, contradicting its lexicographic rule. Hence every cycle is output. The source tabulates two such Hamiltonian paths for $N=16$, $d=2$; the number of cross-join neighbours varies from cycle to cycle, so no degree-based Hamiltonicity criterion applies.

## Sources

- Abbas Alhakim, "Hamiltonicity of the Cross-Join Graph of de Bruijn Sequences", arXiv:1805.12059 (2018), Section 2 (cross-join method), Section 3 (Definitions 3.1-3.2, Lemmas 3.3-3.5), Section 4 (Definition 4.1, Lemma 4.2, Theorem 4.3), Section 5 (Algorithm H and its proof of correctness), <https://doi.org/10.48550/arXiv.1805.12059>.
