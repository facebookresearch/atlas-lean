# Colonization time of the Moran process on graphs

**Setting.** Let $G$ be a graph (directed or undirected) on $n$ nodes in which every node is reachable from the initial mutant node $v$. Consider the Moran birth–death process in the limit of infinite mutant advantage, $r\to\infty$: residents have fitness $0$ and never reproduce, so mutants colonize an otherwise empty environment. Each step picks a node $u$ uniformly at random; if $u$ is a mutant, it places a mutant offspring on a uniformly random out-neighbour $u'$ of $u$ (a change only if $u'$ was a resident); if $u$ is a resident nothing happens. The *colonization time* $T(G,v)$ is the expected number of steps (including idle ones) until all nodes are mutants, and $T(G)=\max_vT(G,v)$.

**Theorem.**
1. For every graph on $n$ nodes, $T(G)\le\tfrac12n^3-\tfrac12n^2$, and the bound is attained: for the *backward graph* $B_n$ (a directed path $1\to2\to\dots\to n$ plus every edge $j\to i$ with $i<j$), $T(B_n,1)=\tfrac12n^3-\tfrac12n^2$.
2. For every undirected graph, $T(G)\le4n^{5/2}+o(n^{5/2})$.
3. For every regular undirected graph, $T(G)=O(n^2)$.
4. The colonization time is always $\Omega(n\log n)$, attained in order by the complete graph; the transitive tournament (all edges from left to right) has $T=\Theta(n^2)$.

In contrast, with residents that reproduce ($r<\infty$) the expected absorption time can be exponential in $n$ on directed graphs.

## Depends on

- [Worst-case absorption time of the Moran process on graphs](worst-case-absorption-time-on-graphs.md)

## Expansion

Split the process into $n-1$ stages, stage $k$ ending when the $(k+1)$-st mutant appears. In a step, a new mutant is created with probability $P_k=\frac1n\sum_{m\in M}\frac{a(m)}{\deg(m)}$, where $a(m)$ is the number of resident out-neighbours of $m$; so stage $k$ lasts $1/P_k$ steps in expectation, and $T=\sum_k\mathbb E[1/P_k]$. Since some mutant has a resident out-neighbour, $P_k\ge\frac1{n\deg_{\max}}\ge\frac1{n(n-1)}$, which already gives $O(n^3)$; in $B_n$ started from node $1$ the mutant set is always $\{1,\dots,k\}$, whose only edge to a resident is the forward edge of node $k$, which has out-degree $k$; hence $P_k=\frac1{nk}$ and $T=\sum_{k=1}^{n-1}nk=\tfrac12n^3-\tfrac12n^2$. For undirected graphs a finer accounting of the degrees of active vertices (a high-degree bottleneck vertex, once colonized, reaches many residents) improves this to $n^{5/2}$; in regular graphs all degrees are equal and $P_k\ge\frac{\#\text{active edges}}{nd}$ gives $O(n^2)$.

## Sources

- Lenka Kopfová and Josef Tkadlec, "Colonization times in Moran process on graphs", PLOS Comput. Biol. 21 (2025), e1012868, <https://doi.org/10.1371/journal.pcbi.1012868>. Numbering follows the arXiv version, arXiv:2410.09476 (2024): Results section (definitions of the $r\to\infty$ Moran process and colonization time, Theorems 1–4) and the supplementary sections on general, regular and undirected bounds, <https://doi.org/10.48550/arXiv.2410.09476>.
