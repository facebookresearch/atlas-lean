# Graph pigeonhole and perfect matching formulas over sparse graphs are hard for resolution

Functional pigeonhole formulas over random bipartite graphs with polynomially many pigeons and constant left degree, and perfect matching formulas over sparse unbalanced expanders, require resolution refutations of length $\exp(n^{1-\epsilon})$ or similar.

For a bipartite graph $G = (U \cup V, E)$ with pigeons $U = [m]$, holes $V = [n]$, $m \ge n + 1$ and neighbourhoods $N(i)$, the **graph PHP formula** has variables $x_{ij}$ for $(i, j) \in E$, pigeon axioms $\bigvee_{j \in N(i)} x_{ij}$ for $i \in [m]$ and hole axioms $\overline{x}_{ij} \lor \overline{x}_{i'j}$ for $i \ne i'$ and $j \in N(i) \cap N(i')$. Adding functionality axioms $\overline{x}_{ij} \lor \overline{x}_{ij'}$ ($j \ne j' \in N(i)$) gives $\mathrm{FPHP}(G)$, and adding also onto axioms $\bigvee_{i \in N(j)} x_{ij}$ for $j \in [n]$ gives the **perfect matching formula** $\mathrm{PM}(G)$. Let $\mathcal{G}(m, n, \Delta)$ be the distribution of bipartite graphs in which each left vertex picks a uniformly random set of $\Delta$ right neighbours.

**Theorem.**

1. Let $k$ and $n$ be positive integers, $\epsilon > 0$ and $m = n^k$. For $G \sim \mathcal{G}(m, n, \Delta)$ with left degree $\Delta = \lceil 16 k^2 / \epsilon \rceil$, asymptotically almost surely every resolution refutation of $\mathrm{FPHP}(G)$ has length $\exp(\Omega(n^{1-\epsilon}))$.
2. Let $m \le n^{o(\log n)}$. For $G \sim \mathcal{G}(m, n, \log m)$, asymptotically almost surely every resolution refutation of $\mathrm{FPHP}(G)$ has length $\exp(\Omega(n^{1-o(1)}))$.
3. Let $m \le n^{o(\log n)}$. For $G \sim \mathcal{G}(m, n, 8 \log^2 m)$, asymptotically almost surely every resolution refutation of $\mathrm{PM}(G)$ has length $\exp(\Omega(n^{1-o(1)}))$.
4. For every constant $\epsilon > 0$ there are explicitly constructible bipartite graphs with $m = \exp(O(n^{1/16}))$ left vertices and left degree polylogarithmic in $m$ whose perfect matching formulas require resolution length $\exp(\Omega(n^{1/8-\epsilon}))$.

## Expansion

The proof extends Razborov's pseudo-width method from dense to sparse graphs. A clause has large pigeon weight on pigeon $i$ when it mentions many holes of $N(i)$; one shows that any short refutation can be turned into one in which every clause has small pseudo-width, after which a separate argument shows that small pseudo-width refutations of a good boundary expander cannot exist. To survive adversarial restrictions in sparse graphs, the argument repeatedly takes the closure of a small set of right vertices, restoring boundary expansion; for perfect matching formulas a preprocessing step as in Razborov's onto-FPHP lower bound is added. Expansion of random graphs comes from a union bound (Lemma 4); the explicit graphs come from unbalanced expander constructions.

## Depends on

- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

None.

## Sources

- S. F. de Rezende, J. Nordström, K. Risse, D. Sokolov, "Exponential resolution lower bounds for weak pigeonhole principle and perfect matching formulas over sparse graphs", *CCC 2020*, LIPIcs 169, 28:1-28:24, doi:10.4230/LIPIcs.CCC.2020.28 (Theorems 1-3 in Section 1.2, Corollaries 16 and 17 in Section 4, Corollaries 26 and 27 in Section 5, Lemma 4 and Definition 11).
