# Uniform linear-time sampling of RNA pseudoknot structures of fixed genus

**Genus of an RNA diagram.** Draw an RNA structure with $n$ base pairs as a diagram: a horizontal backbone with $n$ arcs in the upper half-plane. Thicken the backbone to a disc and the arcs to ribbons to obtain a fatgraph whose surface has $r$ boundary components. Its Euler characteristic gives the **topological genus**

$$2-2g-r=1-n,$$

so $g$ follows directly from counting boundary components. Secondary structures are exactly the diagrams of genus $0$, and pseudoknots raise the genus; for fixed $g$ there are finitely many shapes (irreducible pseudoknot types). Collapsing the backbone to a vertex and passing to the dual map identifies diagrams with $n$ arcs and genus $g$ with rooted unicellular (one-face) maps of genus $g$ with $n$ edges. Their number $\epsilon_g(n)$ is therefore the number of perfect matchings of genus $g$ on $2n$ points.

**Theorem.**

*(1)* (Chapuy's trisection bijection) A unicellular map of genus $g$ has exactly $2g$ trisections. There is a bijection between pairs (map of genus $g$, trisection) and the disjoint union over $k<g$ of tuples (map of genus $k$, set of $2g-2k+1$ distinct vertices). Consequently

$$2g\,\epsilon_g(n)=\binom{n+1-2(g-1)}3\epsilon_{g-1}(n)+\dots+\binom{n+1}{2g+1}\epsilon_0(n),$$

$$\epsilon_g(n)=\sum_{0=g_0<g_1<\dots<g_r=g}\ \prod_{i=1}^r\frac1{2g_i}\binom{n+1-2g_{i-1}}{2(g_i-g_{i-1})+1}\cdot\frac1{n+1}\binom{2n}n .$$

*(2)* (Uniform sampler) Draw a uniform plane tree with $n$ edges, then repeatedly glue vertices to raise the genus along a path $0=g_0<g_1<\dots<g_r=g$ chosen with probabilities proportional to the summands above. The result is a uniformly distributed unicellular map, and hence a uniformly distributed RNA diagram, of genus $g$ with $n$ arcs. The algorithm runs in time linear in $n$ for each fixed $g$.

*(3)* (Energy-weighted sampler) For a simplified loop-based energy of the planar skeleton, computing the partition function once in $O(n^2)$ time allows Boltzmann-weighted structures of genus $g$ to be sampled in linear time each.

## Expansion

Gluing three distinct vertices of a unicellular map of genus $g$ into one keeps a single face and raises the genus by one, since the vertex count drops by $2$ while edges and faces are unchanged. Chapuy's bijection inverts this operation canonically by marking a trisection, which accounts for the factor $2g$ (the number of trisections). Iterating it from a uniform plane tree, which can be sampled in linear time by standard Catalan samplers, gives exact uniformity without rejection. For RNA this replaces grammar-based approaches, whose cost grows with the complexity of the pseudoknot classes they allow, by a topological filtration in which every structure of a given genus is reachable.

## Sources

- Fenix W. D. Huang, Markus E. Nebel, Christian M. Reidys, "Uniform generation of RNA pseudoknot structures with genus filtration", arXiv:1304.7397 (2013), Section 2 (fatgraphs, genus formula $2-2g-r=1-n$), Proposition 1, Theorem 1 (after Chapuy), Corollaries 1–2, sampling algorithm and complexity analysis (Sections 3–4), <https://doi.org/10.48550/arXiv.1304.7397>.
