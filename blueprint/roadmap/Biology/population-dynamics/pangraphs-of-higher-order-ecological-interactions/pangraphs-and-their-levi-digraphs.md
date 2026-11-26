# Pangraphs and their Levi digraphs

**Nested edge sets.** For a finite set $V$ of *fundamental vertices* (species), let $\mathbb P^*(S)$ denote the non-empty subsets of $S$ and define recursively

$$P_0(V) = V, \qquad P_k(V) = \mathbb P^*\Big(\bigcup_{i<k} P_i(V)\Big) \times \mathbb P^*\Big(\bigcup_{i<k} P_i(V)\Big), \quad k \ge 1,$$

an ascending family for $k \ge 1$.

**Pangraph.** An (unweighted) *$k_0$-depth pangraph* is a pair $\mathcal P = (V, E_{\mathcal P})$ with $E_{\mathcal P} \subseteq P_{k_0}(V)$ a set of *panedges* $e = (e^{\mathrm{in}}, e^{\mathrm{out}})$ such that every head and tail is made of fundamental vertices or other panedges: $e^{\mathrm{in}}, e^{\mathrm{out}} \subseteq V \cup E_{\mathcal P}$. Weighted pangraphs add real-valued in- and out-incidence matrices recording the strength and role of each constituent. The *depth* of a panedge is $D(e) = \min\{k : e \in P_k(V)\}$, equivalently $D(e) = 1 + \max\{D(w) : w \in e^{\mathrm{in}} \cup e^{\mathrm{out}}\}$ with $D = 0$ on $V$. A digraph is a pangraph whose panedges join single vertices, and a $1$-depth pangraph is exactly a directed hypergraph (dihypergraph); ubergraphs and other proposed higher-order structures are further special cases.

**Levi digraph.** The incidence representation of a $k_0$-depth pangraph is the multilayer digraph $\mathcal L(\mathcal P)$ with vertex set $V \cup E_{\mathcal P}$, layers $L_j = \{w : D(w) = j - 1\}$ for $j = 1, \dots, k_0 + 1$, and an arc $w \to e$ whenever $w \in e^{\mathrm{in}}$ and an arc $e \to w$ whenever $w \in e^{\mathrm{out}}$, weighted by the corresponding incidence entries. It is unique, and bipartite exactly when $k_0 = 1$.

**Theorem 1 (which layered digraphs are Levi digraphs).** A weighted multilayer digraph $\mathcal G_L$ without multiple edges is the incidence representation of a $k_0$-depth pangraph if and only if, after some permutation of its $k_0 + 1$ layers, its in-adjacency matrix written in layer blocks $(\mathbb A_{ij})$ satisfies:

1. every diagonal block $\mathbb A_{ii}$ is zero (no arcs within a layer);
2. every vertex in a layer $L_l$, $l \ge 2$, has an arc from some vertex in a strictly lower layer;
3. every vertex in a layer $L_l$, $l \ge 2$, has an arc to some vertex in a strictly lower layer.

When exactly one layer ordering satisfies conditions 2 and 3, the pangraph realization is unique.

## Expansion

A vertex of layer $l \ge 2$ in $\mathcal L(\mathcal P)$ is a panedge of depth $l - 1$; it must have a non-empty tail and a non-empty head, each containing at least one constituent of depth exactly $l - 2$ or lower, which gives conditions 2 and 3, and since constituents are never panedges of the same depth as the edge they build, no arcs stay within a layer. Conversely, given a layered digraph meeting the conditions, declare the first layer to be the fundamental vertices and read each higher-layer vertex as the panedge whose tail is its in-neighbors and whose head is its out-neighbors; the layer conditions guarantee the recursive membership $e \in P_{D(e)}(V)$. In an ecological reading, a panedge from a predator to the edge "herbivore eats plant" encodes an interaction modification whose target is a trophic link rather than a species.

## Sources

- M. Iskrzyński, A. Puchalska, A. Grzelik, G. Mutlu, "Pangraphs as models of higher-order interactions" (2025), Section 3.1 (definition of pangraphs and panedge depth), Section 3.2 (Levi digraph definition and Theorem 1), <https://doi.org/10.48550/arXiv.2502.10141>.
