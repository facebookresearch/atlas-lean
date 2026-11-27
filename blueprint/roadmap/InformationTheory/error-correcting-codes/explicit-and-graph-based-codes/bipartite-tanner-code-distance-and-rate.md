# Distance delta(delta - lambda) and rate of bipartite Tanner codes

Let $B$ be a $D$-regular bipartite multigraph between $L$ and $R$ with normalized nontrivial singular value $\sigma_2(B) \le \lambda$, and let the local codes $C_L, C_R \subseteq \alpha^D$ have relative distance at least $\delta \ge 0$ (distinct local codewords differ in at least $\delta D$ positions). Then any two distinct words of the bipartite Tanner code differ on at least

$$\delta(\delta - \lambda)\, |L|\, D$$

edges, a relative distance of $\delta(\delta - \lambda)$. If $C_L, C_R$ are linear over a finite ring, the Tanner code has rate at least $\mathrm{rate}(C_L) + \mathrm{rate}(C_R) - 1$.

## Proof sketch

Let $S \subseteq L$ and $T \subseteq R$ be the vertices touching edges where the two words differ. Each such vertex sees at least $\delta D$ differing edges, so the number $e$ of differing edges satisfies $e \ge \delta D |S|$ and $e \ge \delta D |T|$, while $e \le e(S, T)$. The bipartite mixing lemma gives $e(S, T) \le D|S||T|/N + \lambda D\sqrt{|S||T|}$, and combining these forces $e \ge \delta(\delta - \lambda) N D$. The rate bound counts constraints: each side imposes at most $(1 - \mathrm{rate})$ of the edge coordinates.

## Depends on

- [Bipartite Tanner codes on regular bipartite multigraphs](bipartite-tanner-code.md)
- [Bipartite expander mixing lemma for regular bipartite multigraphs](../../../GraphTheory/graph-families-and-operations/expander-graph-operations/bipartite-expander-mixing-lemma.md)

## Proof depends on

- [Bipartite expander mixing lemma for regular bipartite multigraphs](../../../GraphTheory/graph-families-and-operations/expander-graph-operations/bipartite-expander-mixing-lemma.md)

## Sources

- R. M. Tanner, "A Recursive Approach to Low Complexity Codes", IEEE Transactions on Information Theory, 1981.
- M. Sipser, D. A. Spielman, "Expander Codes", IEEE Transactions on Information Theory, 1996.
- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
