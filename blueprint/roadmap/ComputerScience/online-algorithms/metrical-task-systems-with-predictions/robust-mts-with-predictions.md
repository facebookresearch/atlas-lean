# Robust learning-augmented algorithms for metrical task systems

For every metrical task system that admits a deterministic $c$-competitive online algorithm, there is a deterministic algorithm using predicted states with competitive ratio $O\!\left(\min\left\{1 + \frac{\eta}{\mathrm{OPT}},\; c\right\}\right)$; if the MTS admits a randomized $c$-competitive algorithm, then for every $\varepsilon > 0$ there is a randomized algorithm with ratio $(1 + \varepsilon)\min\left\{1 + O\!\left(\frac{\eta}{\mathrm{OPT}}\right),\; c\right\}$ up to an additive term proportional to the diameter.

## Proof sketch

Combine Follow-the-Prediction, whose cost is $\mathrm{OPT} + O(\eta)$, with the $c$-competitive algorithm using the deterministic or randomized combination lemma for metrical task systems.

## Depends on

- [Following the predictions costs $\mathrm{OPT} + O(\eta)$](follow-the-prediction.md)
- [Combining online algorithms for metrical task systems](../learning-augmented-caching/combining-online-algorithms.md)

## Proof depends on

- [Following the predictions costs $\mathrm{OPT} + O(\eta)$](follow-the-prediction.md)
- [Combining online algorithms for metrical task systems](../learning-augmented-caching/combining-online-algorithms.md)

## Sources

- Antonios Antoniadis, Christian Coester, Marek Eliáš, Adam Polak, Bertrand Simon, "Online Metric Algorithms with Untrusted Predictions", ICML (2020); ACM Transactions on Algorithms 19(2) (2023), arXiv:2003.02144.
- Avrim Blum, Carl Burch, "On-Line Learning and the Metrical Task System Problem", Machine Learning 39(1) (2000).
