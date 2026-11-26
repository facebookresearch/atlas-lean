# Following the predictions costs $\mathrm{OPT} + O(\eta)$

For metrical task systems with predicted states, the algorithm *Follow-the-Prediction*, which at each time moves to the state $x_t$ minimizing $\ell_t(x) + d(x, p_t)$ (with ties broken by proximity to $p_t$), has cost at most $\mathrm{OPT} + O(\eta)$; in particular it is $1$-consistent.

## Proof sketch

Compare with the optimal solution $o_t$: by the choice of $x_t$, $\ell_t(x_t) + d(x_t, p_t) \le \ell_t(o_t) + d(o_t, p_t)$. The movement $d(x_{t-1}, x_t)$ is at most $d(x_{t-1}, p_{t-1}) + d(p_{t-1}, o_{t-1}) + d(o_{t-1}, o_t) + d(o_t, p_t) + d(p_t, x_t)$ by the triangle inequality; summing over $t$ and using the previous inequality to absorb the terms $d(x_t, p_t)$ bounds the total by $\mathrm{OPT} + O(\sum_t d(p_t, o_t))$.

## Depends on

- [Metrical task systems with predicted states](mts-with-state-predictions.md)

## Proof depends on

- [Metrical task systems with predicted states](mts-with-state-predictions.md)

## Sources

- Antonios Antoniadis, Christian Coester, Marek Eliáš, Adam Polak, Bertrand Simon, "Online Metric Algorithms with Untrusted Predictions", ICML (2020); ACM Transactions on Algorithms 19(2) (2023), arXiv:2003.02144.
