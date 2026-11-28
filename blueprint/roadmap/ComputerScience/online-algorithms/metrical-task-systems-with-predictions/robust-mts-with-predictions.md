# Robust learning-augmented algorithms for metrical task systems

If a metrical task system admits a deterministic $\alpha$-competitive online algorithm, then given predicted states there is a deterministic algorithm with competitive ratio

$$
9 \cdot \min\left\{\alpha,\; 1 + \frac{4\eta}{\mathrm{Off}}\right\}
$$

against every offline algorithm $\mathrm{Off}$, where $\eta$ is the prediction error with respect to $\mathrm{Off}$. If it admits a randomized $\alpha$-competitive algorithm and its metric has diameter $D$, then for every $\varepsilon \in (0, 1/4]$ there is a randomized algorithm with expected cost at most

$$
(1 + \varepsilon)\min\left\{\alpha,\; 1 + \frac{4\eta}{\mathrm{Off}}\right\}\mathrm{Off} + O\!\left(\frac{D}{\varepsilon}\right).
$$

The linear dependence on $\eta/\mathrm{Off}$ cannot be improved in general: it is tight up to constant factors for some metrical task systems on uniform metrics.

## Proof sketch

Combine Follow-the-Prediction, whose cost is at most $\mathrm{Off} + 4\eta$, with the $\alpha$-competitive algorithm using the deterministic combination of Fiat, Rabani and Ravid (factor $9$ for two algorithms) or the randomized combination of Blum and Burch.

## Depends on

- [Metrical task systems with predicted states](mts-with-state-predictions.md)

## Proof depends on

- [Following the predictions costs $\mathrm{OPT} + 4\eta$](follow-the-prediction.md)
- [Combining online algorithms for metrical task systems](../learning-augmented-caching/combining-online-algorithms.md)

## Sources

- Antonios Antoniadis, Christian Coester, Marek Eliáš, Adam Polak, Bertrand Simon, "Online Metric Algorithms with Untrusted Predictions", ICML (2020); ACM Transactions on Algorithms 19(2) (2023), arXiv:2003.02144, Theorems 1, 2 and 20.
- Avrim Blum, Carl Burch, "On-Line Learning and the Metrical Task System Problem", Machine Learning 39(1) (2000).
