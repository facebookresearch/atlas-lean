# Perfect phylogeny is polynomial for a bounded number of states

Let $S = \{s_1, \dots, s_n\}$ be a set of objects and $C = \{c_1, \dots, c_m\}$ a set of characters, each $c_j$ a function from $S$ to $\{0, 1, \dots, r_j - 1\}$, and let $r = \max_j r_j$. A phylogeny for $S$ is an unrooted tree whose leaves are bijectively labelled by $S$; it is a perfect phylogeny for $(S, C)$ if for each character $c_j$ and each pair of distinct states $\alpha \ne \beta$, the minimal subtrees connecting the objects with state $\alpha$ and those with state $\beta$ are vertex-disjoint. Agarwala and Fernández-Baca (1994) give an algorithm that decides whether a perfect phylogeny exists and constructs one if so in time $O(2^{3r}(nm^3 + m^4))$ for $n$ objects and $m$ characters with at most $r$ states each (as summarized in Kannan and Warnow 1997). Hence the problem is solvable in polynomial time when every character has $O(\log(m + n))$ allowed states, and in particular for every fixed bound on the number of states, while it is NP-complete in general (Bodlaender, Fellows and Warnow 1992; Steel 1992).

## Expansion

1. Definitions: character state matrices, phylogenies, and perfect phylogenies via vertex-disjoint minimal subtrees.
2. The subsets of objects (c-clusters) on which Agarwala and Fernández-Baca build perfect phylogenies bottom-up.
3. Their dynamic program and its running time $O(2^{3r}(nm^3 + m^4))$.
4. The refinement of Kannan and Warnow (1997) with running time $O(2^{2r}m^2n)$, and their implicit representation of the set of all perfect phylogenies, as separate statements.
5. NP-hardness for unbounded $r$, as a separate statement; the binary case is [Perfect phylogeny and the four-gamete condition](../../../Biology/phylogenetics/splits-compatibility-ultrametrics-and-upgma/exists-perfect-phylogeny-iff.md).

## Sources

- Original result: R. Agarwala and D. Fernández-Baca, A polynomial-time algorithm for the perfect phylogeny problem when the number of character states is fixed, SIAM J. Comput. 23 (1994), 1216–1224. <https://doi.org/10.1137/s0097539793244587>
- S. Kannan and T. Warnow, A fast algorithm for the computation and enumeration of perfect phylogenies, SIAM J. Comput. 26 (1997), 1749–1763. <https://doi.org/10.1137/S0097539794279067>
- H. L. Bodlaender, M. R. Fellows and T. J. Warnow, Two strikes against perfect phylogeny, in *Automata, Languages and Programming (ICALP 1992)*, Lecture Notes in Comput. Sci. 623, Springer, 1992, 273–283.
- M. Steel, The complexity of reconstructing trees from qualitative characters and subtrees, J. Classification 9 (1992), 91–116.
