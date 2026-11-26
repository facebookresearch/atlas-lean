# Fixing flow decomposition MILP variables with incompatible safe sequences

**Flow decomposition problems.** Let $G=(V,E)$ be an $s$-$t$ graph (cycles allowed), $E'\subseteq E$, $f:E\to\mathbb Z_{\ge0}$ edge weights (e.g. read coverage in an assembly graph) and $k\ge1$. One seeks $s$-$t$ walks $W_1,\dots,W_k$ with weights $w_i\in\mathbb Z^+$, where $W_i(uv)$ counts traversals of $uv$:
- $k$-FD: $\sum_iW_i(uv)w_i=f(uv)$ for all $uv\in E'$;
- $k$-LAE: minimize $\sum_{uv\in E'}|f(uv)-\sum_iW_i(uv)w_i|$;
- $k$-MPE: with slacks $\rho_i\ge0$, require $|f(uv)-\sum_iW_i(uv)w_i|\le\sum_iW_i(uv)\rho_i$ on $E'$ and minimize $\sum_i\rho_i$.
In the MILPs each walk is encoded by integer variables $x_{uv,i}=W_i(uv)$.

**Theorem (antichains in graphs with cycles).** Computing a maximum-weight antichain of edges (pairwise mutually unreachable edges maximizing $\sum_{e\in A}w(e)$) in a graph $G$ reduces in $O(|V|+|E|)$ time to the same problem on a DAG $G'$ with $|V'|\le2|V|$, $|E'|\le|E|$, hence is polynomial.

**Variable fixing.** Let $A=\{e_1,\dots,e_t\}$ be an antichain and $S(e_i)$ a safe edge sequence through $e_i$ (for edge-covering solutions). No $s$-$t$ walk contains two of these sequences, so in every solution they lie in distinct walks, $k\ge t$, and after relabelling $S(e_i)\subseteq W_i$. Hence one may set, for $i\le t$ and $uv\in S(e_i)$,

$$x_{uv,i}=1\ \text{ if $uv$ joins different strongly connected components},\qquad x_{uv,i}\ge S(e_i)(uv)\ \text{ if $uv$ lies inside one},$$

make every variable of an inter-component edge binary, and set $x_{uv,i}=0$ for every edge $uv$ such that $v$ does not reach the first vertex of $S(e_i)$, the last vertex of $S(e_i)$ does not reach $u$, and no two consecutive edges $ab,cd$ of $S(e_i)$ have $b$ reaching $u$ and $v$ reaching $c$.

## Depends on

- [Maximal safe sequences as common leaves of dominator trees](maximal-safe-sequences-as-common-leaves-of-dominator-trees.md)

## Expansion

If one walk contained $S(e_i)$ and $S(e_j)$ it would traverse $e_i$ and $e_j$, so one would reach the other, contradicting the antichain property. Inter-component edges can be traversed at most once by a walk because the condensation of strongly connected components is acyclic, while an edge inside a component can be repeated, which justifies the two fixing rules; an edge satisfying none of the three reachability conditions cannot be placed before, after, or between the edges of $S(e_i)$ on walk $i$. For the antichain reduction, edges inside one strongly connected component are mutually reachable, so an antichain uses at most one edge per component; in the condensation DAG each non-trivial component becomes an edge $v'_{in}v'_{out}$ weighted by its heaviest internal edge, and each edge between components becomes a subdivided path whose first edge carries its weight. Antichains of the two graphs then correspond with equal weights, and the DAG problem reduces to a min-flow computation. On de Bruijn graphs from bacterial genomes these reductions shrink the models and remove linearizations of products of integer variables, with reported speed-ups up to $393\times$ (FD), $560\times$ (LAE) and $1465\times$ (MPE).

## Sources

- F. Sena, A. I. Tomescu, "Fast and flexible flow decompositions in general graphs via dominators", arXiv:2511.19153 (2025), <https://doi.org/10.48550/arXiv.2511.19153>. Section 2 (Definition 1), Section 4 (Theorem 7 and the variable-fixing rules), Section 5 (experimental speed-ups) and Appendix A (Lemma 3, Theorem 8).
