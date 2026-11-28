# Generating function of unicellular maps of genus g

**Setting.** A *unicellular map* of genus $g$ is a connected graph embedded in the closed orientable surface of genus $g$ with exactly one face; equivalently a fatgraph (a graph with a cyclic order of half-edges at each vertex) with a single boundary component. All maps counted here are **rooted**: one half-edge $r$ is distinguished, and the facial tour is read starting at $r$. Equivalently, label the $2n$ half-edges $1,\dots,2n$ in the order of the unique facial cycle starting at $r$, so that the map is determined by the pairing of half-edges into edges (the vertex cycles are then the facial cycle composed with this pairing); in the duality with RNA diagrams below, the backbone of the linear diagram supplies this starting half-edge. Rooted genus-$0$ unicellular maps are rooted plane trees, counted by the Catalan numbers $\mathrm{Cat}(n)=\frac{1}{n+1}\binom{2n}{n}$ ($n$ edges); for example there are $\mathrm{Cat}(2)=2$ rooted plane trees with two edges, although only one unrooted plane tree (the path). Unicellular maps are the Poincaré duals of RNA diagrams of genus $g$ (pseudoknotted base-pair diagrams whose fatgraph, with the backbone collapsed to one vertex, has genus $g$), with boundary components of the diagram becoming vertices of the map. Let $C_g(z)=\sum_n\epsilon_g(n)z^n$, where $\epsilon_g(n)$ is the number of rooted unicellular maps of genus $g$ with $n$ edges.

**Theorem.** For $g\ge1$ there are rational coefficients $a^{(g)}_t$ such that, with $\kappa^{(g)}_t=a^{(g)}_t\,\mathrm{Cat}(2g+t)$,

$$C_g(z)=\sum_{t=0}^{g-1}\kappa^{(g)}_t\,\frac{z^{2g+t}}{(1-4z)^{2g+t+\frac12}} .$$

The first values are $\kappa^{(1)}_0=1$; $\kappa^{(2)}_0=21$, $\kappa^{(2)}_1=105$; $\kappa^{(3)}_0=1485$, $\kappa^{(3)}_1=18018$, $\kappa^{(3)}_2=50050$. For example $C_1(z)=z^2(1-4z)^{-5/2}$, giving $1$ rooted genus-one map with $2$ edges and $10$ with $3$ edges.

## Expansion

The proof uses Chapuy's trisection bijection: slicing a labelled vertex of a genus-$g$ unicellular map at a trisection produces a map of lower genus $g-t'$ with $2t'+1$ distinguished vertices, giving the recursion $2g\,\epsilon_g^{(k)}(n)=\sum_{t'\ge1}\big[\binom{k+2t'+1}{2t'+1}\epsilon_{g-t'}^{(k+2t'+1)}(n)+\binom{k+2t'}{2t'+1}\epsilon_{g-t'}^{(k+2t')}(n)\big]$ for maps with $k$ labelled vertices. Iterating down to genus $0$ expresses $C_g$ as a combination of generating functions of plane trees with $2g+t+1$ labelled vertices, whose generating functions are $\mathrm{Cat}(2g+t)z^{2g+t}(1-4z)^{-(2g+t+1/2)}$ up to the combinatorial weights $a^{(g)}_t$ collected from the glue paths.

## Sources

- F. W. D. Huang, C. M. Reidys, "Shapes of topological RNA structures", arXiv:1403.2908 (2014), Section "Some basic facts" (Theorem 1, after Chapuy), Section "Unicellular maps of genus $g$": Lemma 2, Theorem 2 and its table of $\kappa^{(g)}_t$, <https://doi.org/10.48550/arXiv.1403.2908>.
