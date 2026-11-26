# Genus-slicing bijection for bicellular maps and uniform generation of RNA-RNA complexes

**Objects.** An RNA-RNA interaction structure of two strands is a planted *2-backbone diagram*: two backbones with arcs (base pairs) within and between them, crossings allowed. Inflating the arcs to ribbons and collapsing each backbone to a vertex gives a fat graph with two vertices, i.e. a map $\mathfrak{m} = (\gamma,\alpha,\sigma)$ given by permutations of half-edges, with genus $g$ determined by $|\sigma| + |\gamma| = |\alpha| + 2 - 2g$. Its Poincaré dual, which swaps vertices and boundary components, is a **bicellular map**; this is a genus-preserving bijection between planted 2-backbone diagrams and planted bicellular maps. Unicellular maps play the same role for a single strand. A half-edge $h$ is a *trisection* if it is a down-step ($\sigma(h) \le_\gamma h$) and $\sigma(h)$ is not the minimum half-edge of its vertex.

**Theorem.**

*(1)* (Trisection count) Every planted bicellular map of genus $g$ has exactly $2(g+1)$ trisections.

*(2)* (Slicing bijection) Let $D_{b,g}(n)$ be the bicellular maps of genus $g$ with $n$ edges and a distinguished trisection, $B_p(n)^t$ bicellular maps of genus $p$ with $t$ distinguished vertices, and $(U_{g_1}(m), U_{p-g_1}(n-m))^t$ pairs of unicellular maps with $t$ distinguished vertices. There is an explicit bijection

$$\Xi_b : D_{b,g}(n) \to \Big(\dot\bigcup_{p=0}^{g-1}B_p(n)^{2g-2p+1}\Big)\ \dot\cup\ \Big(\dot\bigcup_{p=0}^{g}\dot\bigcup_{g_1=0}^{p}\dot\bigcup_{m=0}^{n}\big(U_{g_1}(m), U_{p-g_1}(n-m)\big)^{2g-2p+3}\Big):$$

slicing either lowers the genus of the bicellular map or disconnects it into a pair of single-stranded structures.

*(3)* (Recursion) Consequently, with $\mathsf{B}_g(n)$ and $\mathsf{U}_g(n)$ the numbers of such maps, $\mu_{g_1} = m + 1 - 2g_1$ and $\nu_{g_1,i} = n - m - 2i + 2g_1 + 1$,

$$2(g+1)\mathsf{B}_g(n) = \sum_{i=0}^{g-1}\binom{n-2i}{2g-2i+1}\mathsf{B}_i(n) + \sum_{i=0}^{g}\sum_{g_1=0}^{i}\sum_{m=0}^{n}\sum_{k=1}^{2g-2i+2}\binom{\mu_{g_1}}{k}\binom{\nu_{g_1,i}}{2g-2i+3-k}\mathsf{U}_{g_1}(m)\,\mathsf{U}_{i-g_1}(n-m),$$

and iterating the slicing reduces every bicellular map to a pair of planar trees.

*(4)* (Uniform sampling) Running the bijection backwards from uniformly sampled planar trees ("genus induction") generates bicellular maps of fixed genus $g$ uniformly at random in linear time.

## Expansion

This extends Chapuy's trisection bijection for unicellular maps: a unicellular map of genus $g$ has $2g$ trisections, and gluing at a trisection changes the genus by one. In a bicellular map the extra boundary component gives two more trisections, and a slice either stays bicellular with smaller genus or separates the two cells, producing two unicellular maps, i.e. two single-stranded RNA structures. Counting the preimages ($2(g+1)$ choices of trisection on the left, choices of distinguished vertices on the right) gives the recursion, and since every bicellular map of genus $g$ is produced with the same multiplicity $2(g+1)$, inverting the bijection from uniform inputs gives uniform outputs. The decomposition grammar also supports loop-energy based sampling of RNA complexes filtered by topological genus.

## Sources

- Benjamin Mingming Fu, Hillary Siwei Han and Christian M. Reidys, "Uniform generation of RNA-RNA interaction structures of fixed topological genus", arXiv:1311.0684 (2013), Lemmas 1 and 2, Section 4 (Theorem 1, Corollaries 1-2) and Section 5 (Corollary 3), <https://doi.org/10.48550/arXiv.1311.0684>.
