# Perfect phylogeny is polynomial for a bounded number of states

Let $S = \{s_1, \dots, s_n\}$ be a set of objects and $C = \{c_1, \dots, c_m\}$ a set of characters, each $c_j$ a function from $S$ to $\{0, 1, \dots, r_j - 1\}$, and let $r = \max_j r_j$. A phylogeny for $S$ is an unrooted tree whose leaves are bijectively labelled by $S$; it is a perfect phylogeny for $(S, C)$ if for each character $c_j$ and each pair of distinct states $\alpha \ne \beta$, the minimal subtrees connecting the objects with state $\alpha$ and those with state $\beta$ are vertex-disjoint. Jansson (2016) records the result of Agarwala and Fernández-Baca: a dynamic program that builds perfect phylogenies bottom-up on c-clusters, subsets $G \subseteq S$ such that $G$ and $S \setminus G$ share at most one state of each character and share no state of at least one character, decides whether a perfect phylogeny exists and constructs one if so in time $O(2^{3r}(nm^3 + m^4))$, the number of c-clusters being at most $2^r m$. Hence the problem is solvable in polynomial time when every character has $O(\log(m + n))$ allowed states, and in particular for every fixed bound on the number of states, while it is NP-hard in general (Bodlaender, Fellows and Warnow; Steel).

## Expansion

1. Definitions: character state matrices, phylogenies, and perfect phylogenies via vertex-disjoint minimal subtrees.
2. c-clusters, their two defining properties, and the bound $2^r m$ on their number.
3. The bottom-up dynamic program over c-clusters and its running time $O(2^{3r}(nm^3 + m^4))$.
4. The refinement of Kannan and Warnow with running time $O(2^{2r}nm^2)$ and the enumeration of all minimal perfect phylogenies, as recorded by Jansson, as separate statements.
5. NP-hardness for unbounded $r$, as a separate statement; the binary case is [Perfect phylogeny and the four-gamete condition](../../../Biology/phylogenetics/splits-compatibility-ultrametrics-and-upgma/exists-perfect-phylogeny-iff.md).

## Sources

- J. Jansson, Perfect phylogeny (bounded number of states), in *Encyclopedia of Algorithms*, 2nd ed., Springer, 2016, 1550–1553, Problem 1, Theorems 1–3. <https://doi.org/10.1007/978-1-4939-2864-4_288>
- Original result: R. Agarwala and D. Fernández-Baca, A polynomial-time algorithm for the perfect phylogeny problem when the number of character states is fixed, SIAM J. Comput. 23 (1994), 1216–1224. <https://doi.org/10.1137/s0097539793244587> The algorithm and its running time follow Jansson (2016).
