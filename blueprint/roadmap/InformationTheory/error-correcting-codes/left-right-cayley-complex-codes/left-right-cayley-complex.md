# Left-right Cayley complexes

Let $G$ be a finite group and $A, B \subseteq G \setminus \{1\}$ symmetric generating sets ($A = A^{-1}$, $B = B^{-1}$), with $|A| = |B| = \Delta$, satisfying the total no-conjugacy condition $ag \ne gb$ for all $g \in G$, $a \in A$, $b \in B$. The **left-right Cayley complex** $\mathrm{Cay}^2(A, G, B)$ is the square complex with

- vertex set $G$;
- **$A$-edges** $\{g, ag\}$ and **$B$-edges** $\{g, gb\}$ for $g \in G$, $a \in A$, $b \in B$;
- **squares** $\{g, ag, gb, agb\}$ for $g \in G$, $a \in A$, $b \in B$.

Because left and right multiplications commute, and by the total no-conjugacy condition, every square has four distinct vertices and every vertex lies in exactly $\Delta^2$ squares, and the link of each vertex is the complete bipartite graph $K_{\Delta, \Delta}$ with sides $A$ and $B$. The $A$-edges form the Cayley graph $\mathrm{Cay}(G, A)$ acting on the left and the $B$-edges form $\mathrm{Cay}(G, B)$ acting on the right.

## Depends on

- [Cayley digraph](../../../GraphTheory/algebraic-graph-theory/part-01/directed-cayley-graph.md)
- [Spectral expander](../../../GraphTheory/graph-families-and-operations/expander-graphs/is-spectral-expander.md)

## Sources

- I. Dinur, S. Evra, R. Livne, A. Lubotzky, S. Mozes, "Locally testable codes with constant rate, distance, and locality", STOC (2022), arXiv:2111.04808.
- O. Goldreich, "On the locally testable code of Dinur et al. (2021)", ECCC TR21-175 (2021).
