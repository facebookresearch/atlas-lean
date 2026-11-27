# Core-tail decomposition of the optimal revenue

For a single additive buyer with independent values and any thresholds $t_1, \dots, t_n \ge 0$, call item $j$ in the tail when $v_j > t_j$ and in the core otherwise, and let $p_j = \Pr[v_j > t_j]$. Then

$$
\mathrm{REV}(D) \le \sum_{A \subseteq [n]} \Pr[\text{exactly the items in } A \text{ have } v_j > t_j]\, \mathrm{REV}(D_A^{\mathrm{tail}}) + \mathrm{VAL}(D^{\mathrm{core}}),
$$

where the sum runs over the sets $A$ of positive probability $p_A = \prod_{j \in A} p_j \prod_{j \notin A} (1 - p_j)$ (terms with $p_A = 0$ contribute nothing), $D_A^{\mathrm{tail}}$ is the product of the conditional distributions of the items $j \in A$ given $v_j > t_j$, which are well defined because $p_A > 0$ forces $p_j > 0$ for $j \in A$, and $\mathrm{VAL}(D^{\mathrm{core}}) = \sum_j \mathbb{E}[v_j \mid v_j \le t_j]$ is the expected welfare of the core $D^{\mathrm{core}}$, the product of the conditional distributions of all items given $v_j \le t_j$. As in Babaioff et al., a distribution conditioned on an event of probability $0$ is replaced by the point mass at $0$; so an item with $p_j = 1$ contributes $0$ to $\mathrm{VAL}(D^{\mathrm{core}})$, and the conditional tail law of an item with $p_j = 0$ is never used. Choosing $t_j$ so that $\sum_j p_j \le 1$ (for instance $t_j = \mathrm{SREV}(D)$ for every $j$) yields $\mathrm{REV} \le 2\, \mathrm{SREV} + \mathrm{VAL}(D^{\mathrm{core}})$.

## Proof sketch

Partitioning the type space by the set $A$ of tail items gives $\mathrm{REV}(D) \le \sum_A p_A \mathrm{REV}(D_A)$, where $D_A$ is the product of the core of the items outside $A$ and the tail of those in $A$, and $\mathrm{REV}(D' \times D'') \le \mathrm{VAL}(D') + \mathrm{REV}(D'')$ for independent $D', D''$ bounds each term by the core welfare plus the tail revenue; the core welfare of the items outside $A$ is at most $\mathrm{VAL}(D^{\mathrm{core}})$. For the tail, $\mathrm{REV}(D_A^{\mathrm{tail}}) \le |A|\, \mathrm{SREV}(D_A^{\mathrm{tail}}) \le |A| \sum_{j \in A} r_j / p_j$ with $r_j$ the optimal revenue of item $j$, where every $j \in A$ has $p_j > 0$, and summing over the sets $A$ with $p_A > 0$ gives $\sum_j r_j\, \mathbb{E}[\,|A| \mid j \in A\,] = \sum_j r_j (1 + \sum_{k \ne j} p_k) \le 2\, \mathrm{SREV}$.

## Depends on

- [Single additive buyer with independent item values: SREV, BREV and REV](additive-buyer-srev-brev-rev.md)

## Sources

- M. Babaioff, N. Immorlica, B. Lucier, S. M. Weinberg, "A Simple and Approximately Optimal Mechanism for an Additive Buyer", FOCS 2014; Journal of the ACM 67(4) (2020), arXiv:1405.6146, Lemma 6 and Proposition 3.
- X. Li, A. C.-C. Yao, "On revenue maximization for selling multiple independently distributed items", Proceedings of the National Academy of Sciences 110(28) (2013).
