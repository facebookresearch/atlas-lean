# Following the predictions costs $\mathrm{OPT} + 4\eta$

For metrical task systems with predicted states, the algorithm *Follow-the-Prediction* (FtP), which at each time $t$, after receiving the cost function $\ell_t$ and the prediction $p_t$, moves to a state $x_t$ minimizing $\ell_t(x) + 2\,d(x, p_t)$, satisfies $\mathrm{cost}(\mathrm{FtP}) \le \mathrm{cost}(\mathrm{Off}) + 4\eta$ for every offline algorithm $\mathrm{Off}$, where $\eta$ is the prediction error with respect to $\mathrm{Off}$; it is therefore $(1 + 4\eta/\mathrm{Off})$-competitive against $\mathrm{Off}$, and in particular $1$-consistent.

## Proof sketch

Let $o_1, o_2, \dots$ be the states of $\mathrm{Off}$, starting from the common initial state, and let $\mathcal{A}_t$ be the hybrid that follows FtP up to time $t$ and $\mathrm{Off}$ afterwards, so that $\mathcal{A}_0 = \mathrm{Off}$ and $\mathcal{A}_T = \mathrm{FtP}$. The hybrids $\mathcal{A}_t$ and $\mathcal{A}_{t-1}$ differ only at time $t$, so by the triangle inequality $\mathrm{cost}(\mathcal{A}_t) \le \mathrm{cost}(\mathcal{A}_{t-1}) + 2d(o_t, x_t) + \ell_t(x_t) - \ell_t(o_t) \le \mathrm{cost}(\mathcal{A}_{t-1}) + 2d(o_t, p_t) + 2d(p_t, x_t) + \ell_t(x_t) - \ell_t(o_t)$, and the choice of $x_t$ gives $2d(p_t, x_t) + \ell_t(x_t) \le 2d(p_t, o_t) + \ell_t(o_t)$. Hence each step adds at most $4d(o_t, p_t)$, and summing over $t$ gives $\mathrm{Off} + 4\eta$.

## Depends on

- [Metrical task systems with predicted states](mts-with-state-predictions.md)
- [Consistency and robustness of learning-augmented online algorithms](../learning-augmented-caching/consistency-and-robustness.md)

## Sources

- Antonios Antoniadis, Christian Coester, Marek Eliáš, Adam Polak, Bertrand Simon, "Online Metric Algorithms with Untrusted Predictions", ICML (2020); ACM Transactions on Algorithms 19(2) (2023), arXiv:2003.02144, Section 4.1, Lemma 17.
