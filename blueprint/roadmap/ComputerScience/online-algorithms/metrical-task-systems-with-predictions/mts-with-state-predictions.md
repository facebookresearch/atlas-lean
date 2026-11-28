# Metrical task systems with predicted states

In a *metrical task system with predictions* on $(M, d)$, at each time $t$ the algorithm receives, together with the cost function $\ell_t$, a predicted state $p_t \in M$. The prediction error is measured against an offline algorithm $\mathrm{Off}$ with states $o_1, o_2, \dots, o_T$: $\eta = \sum_{t=1}^{T} d(p_t, o_t)$. Guarantees are stated as functions of $\eta/\mathrm{Off}$ that hold against every offline algorithm $\mathrm{Off}$, in particular against an optimal one. For caching, whose states are cache configurations, the predicted states can be encoded by the evicted pages, and next-arrival predictions can be converted into predicted states.

## Depends on

- [Metrical task systems](../metrical-task-systems-and-hst-embeddings/metrical-task-system.md)
- [Consistency and robustness of learning-augmented online algorithms](../learning-augmented-caching/consistency-and-robustness.md)

## Sources

- Antonios Antoniadis, Christian Coester, Marek Eliáš, Adam Polak, Bertrand Simon, "Online Metric Algorithms with Untrusted Predictions", ICML (2020); ACM Transactions on Algorithms 19(2) (2023), arXiv:2003.02144, Section 1, equation (1).
