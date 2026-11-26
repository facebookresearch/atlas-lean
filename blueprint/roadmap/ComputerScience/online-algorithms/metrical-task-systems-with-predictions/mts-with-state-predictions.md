# Metrical task systems with predicted states

In a *metrical task system with predictions* on $(M, d)$, at each time $t$ the algorithm receives, together with the cost function $\ell_t$, a predicted state $p_t \in M$. For an offline optimal solution $o_1, o_2, \dots$, the prediction error is $\eta = \sum_t d(p_t, o_t)$ (taking the optimal solution minimizing this quantity). This setup specializes to caching, $k$-server and convex body chasing by choosing the state spaces accordingly.

## Depends on

- [Metrical task systems](../metrical-task-systems-and-hst-embeddings/metrical-task-system.md)
- [Consistency and robustness of learning-augmented online algorithms](../learning-augmented-caching/consistency-and-robustness.md)

## Sources

- Antonios Antoniadis, Christian Coester, Marek Eliáš, Adam Polak, Bertrand Simon, "Online Metric Algorithms with Untrusted Predictions", ICML (2020); ACM Transactions on Algorithms 19(2) (2023), arXiv:2003.02144.
