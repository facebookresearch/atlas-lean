# Combining online algorithms for metrical task systems

Let $\mathcal{A}_1, \dots, \mathcal{A}_m$ be online algorithms for the same metrical task system on a metric of diameter $D$. There is a deterministic online algorithm whose cost on every input is $O(m) \cdot \min_i \mathrm{cost}(\mathcal{A}_i) + O(mD)$, and for every $\varepsilon \in (0, 1)$ a randomized one whose expected cost is at most $(1 + \varepsilon)\min_i \mathrm{cost}(\mathcal{A}_i) + O(D \log m/\varepsilon)$. For $m = 2$ the deterministic constant can be taken to be $9$.

## Proof sketch

Simulate all algorithms and follow one of them, switching to another (at cost at most $D$) when the followed algorithm's cost exceeds a geometrically increasing budget, as in the doubling strategy for searching on $m$ rays, which gives constant $9$ for two rays. The randomized bound treats the algorithms as experts and runs a multiplicative-weights scheme with a lazy, low-switching sampling of the expert to follow, charging switches to the decrease of the potential.

## Depends on

- [Metrical task systems](../metrical-task-systems-and-hst-embeddings/metrical-task-system.md)
- [Regret of Hedge for losses in the unit interval](../../machine-learning/online-learning-and-boosting/hedge-algorithm/regret-le.md)

## Proof depends on

- [Metrical task systems](../metrical-task-systems-and-hst-embeddings/metrical-task-system.md)
- [Regret of Hedge for losses in the unit interval](../../machine-learning/online-learning-and-boosting/hedge-algorithm/regret-le.md)

## Sources

- Amos Fiat, Yuval Rabani, Yiftach Ravid, "Competitive k-Server Algorithms", Journal of Computer and System Sciences 48(3) (1994).
- Avrim Blum, Carl Burch, "On-Line Learning and the Metrical Task System Problem", Machine Learning 39(1) (2000).
- Antonios Antoniadis, Christian Coester, Marek Eliáš, Adam Polak, Bertrand Simon, "Online Metric Algorithms with Untrusted Predictions", ICML (2020); ACM Transactions on Algorithms 19(2) (2023), arXiv:2003.02144.
