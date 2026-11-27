# NP-completeness of de Bruijn graph read mapping

**Setting.** For a set of strings $S$ over $\Sigma$ and $k \ge 2$, the de Bruijn graph $dBG_k(S)$ has as nodes the $k$-mers occurring in $S$ and an arc $(d, d')$ whenever the $(k-1)$-suffix of $d$ is a prefix of $d'$. A walk $(v_1, \dots, v_l)$ generates the word of length $k + l - 1$ obtained from $v_1$ by appending the last character of each of $v_2, \dots, v_l$; a path is a walk with no repeated node.

**De Bruijn graph read mapping problem (DBGRMP).** Given $S$, $k \ge 2$, a query $q \in \Sigma^*$ with $|q| \ge k$, a cost function $F : \Sigma \times \Sigma \to \mathbb{N}$ and a threshold $t$, decide whether $dBG_k(S)$ has a path of $|q| - k + 1$ nodes whose generated word $m \in \Sigma^{|q|}$ satisfies $C(m, q) = \sum_{i=1}^{|q|} F(m_i, q_i) \le t$.

**Theorem 1.** DBGRMP is NP-complete.

The hardness already holds for $k = 2$, with an alphabet that grows with the instance (the reduction numbers each symbol by a node of the source graph). Consequently practical tools map reads on compacted de Bruijn graphs heuristically, for example by seeding on the $(k-1)$-overlaps between unitigs and extending under Hamming distance.

## Depends on

- [NP-completeness of read mapping on labelled graphs](np-completeness-of-read-mapping-on-labelled-graphs.md)
- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)

## Expansion

The reduction is from GRMP. Each edge label is tagged by the node it leaves, giving symbols $\alpha_i$. A node of the order-2 de Bruijn graph is created for every pair of consecutive edges $(i \to j$ labelled $\alpha$, $j \to l$ labelled $\beta)$ as the word $\alpha_i \beta_j$, and for every edge leaving a node without predecessors two extra words $\Delta_i \sharp_i$ and $\sharp_i \alpha_i$ with fresh letters $\sharp$ and $\Delta$ are added so that such paths can start. The cost function ignores the tags, $F'(\alpha_i, \beta) = F(\alpha, \beta)$. Paths in the source labelled graph and paths in the constructed de Bruijn graph then correspond bijectively with equal mapping cost, so the answer is preserved.

## Sources

- A. Limasset, B. Cazaux, E. Rivals, P. Peterlongo, "Read mapping on de Bruijn graphs", BMC Bioinformatics 17 (2016) 237, Definitions 1-7, Propositions 1-2 and Theorem 1, <https://doi.org/10.1186/s12859-016-1103-9> (PMC4910249).
