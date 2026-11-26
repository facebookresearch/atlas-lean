# Core-tail decomposition of the optimal revenue

For a single additive buyer with independent values and any thresholds $t_1, \dots, t_n \ge 0$, write $v_j = v_j \mathbf{1}[v_j \le t_j] + v_j \mathbf{1}[v_j > t_j]$. Then

$$
\mathrm{REV}(D) \le \sum_{A \subseteq [n]} \Pr[\text{exactly the items in } A \text{ have } v_j > t_j]\, \mathrm{REV}(D_A^{\mathrm{tail}}) + \mathrm{VAL}(D^{\mathrm{core}}),
$$

where $D_A^{\mathrm{tail}}$ is the conditional distribution of the items in $A$ given that they exceed their thresholds and $\mathrm{VAL}(D^{\mathrm{core}}) = \mathbb{E}\bigl[\sum_j v_j \mathbf{1}[v_j \le t_j]\bigr]$ is the expected welfare of the core. Choosing $t_j$ so that $\sum_j \Pr[v_j > t_j] \le 1$ yields $\mathrm{REV} \le 2\, \mathrm{SREV} + \mathrm{VAL}(D^{\mathrm{core}})$.

## Proof sketch

Revenue is subadditive across the partition of the type space according to which items exceed their thresholds, after conditioning; on each part, revenue is at most the revenue from the tail items plus the welfare of the core items (giving the core items away costs at most their value). With $\sum_j \Pr[v_j > t_j] \le 1$, the tail term is bounded via a single-item-at-a-time argument by twice the separate-selling revenue.

## Depends on

- [Single additive buyer with independent item values: SREV, BREV and REV](additive-buyer-srev-brev-rev.md)

## Sources

- M. Babaioff, N. Immorlica, B. Lucier, S. M. Weinberg, "A Simple and Approximately Optimal Mechanism for an Additive Buyer", FOCS 2014; Journal of the ACM 67(4) (2020), arXiv:1405.6146.
- X. Li, A. C.-C. Yao, "On revenue maximization for selling multiple independently distributed items", Proceedings of the National Academy of Sciences 110(28) (2013).
