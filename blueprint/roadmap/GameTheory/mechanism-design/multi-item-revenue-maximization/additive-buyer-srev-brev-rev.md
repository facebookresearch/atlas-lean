# Single additive buyer with independent item values: SREV, BREV and REV

A seller has $n$ heterogeneous items and faces one buyer whose value for item $j$ is $v_j \ge 0$, drawn independently from distributions $D_1, \dots, D_n$; the buyer's value for a set $S$ is $\sum_{j \in S} v_j$. A (truthful, individually rational) mechanism is a menu of lotteries with prices from which the buyer picks a utility-maximizing option. Let $\mathrm{REV}(D)$ be the supremum of expected revenue over all such mechanisms, $\mathrm{SREV}(D) = \sum_j \max_p p \Pr[v_j \ge p]$ the revenue of selling each item separately at its optimal posted price, and $\mathrm{BREV}(D) = \max_p p \Pr[\sum_j v_j \ge p]$ the revenue of selling the grand bundle at its optimal price.

## Depends on

- [Posted-price allocation](../optimal-auctions-and-virtual-valuations/posted-price-alloc.md)
- [Revelation principle (Bayesian, pure strategies)](../revelation-principle/revelation-principle-bayes-nash.md)

## Sources

- M. Babaioff, N. Immorlica, B. Lucier, S. M. Weinberg, "A Simple and Approximately Optimal Mechanism for an Additive Buyer", FOCS 2014; Journal of the ACM 67(4) (2020), arXiv:1405.6146.
- S. Hart, N. Nisan, "Approximate revenue maximization with multiple items", Journal of Economic Theory 172 (2017); EC 2012.
