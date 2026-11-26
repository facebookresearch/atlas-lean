# Blind strategies beat $1 - 1/e$ for prophet secretary

For independent nonnegative values in uniformly random order, there is a *blind* strategy, a single function $\alpha : [0, 1] \to [0, 1]$ such that at time fraction $t$ the gambler accepts a value exceeding the $\alpha(t)$-quantile of the distribution of the maximum, that guarantees $\mathbb{E}[X_\tau] \ge 0.669\, \mathbb{E}[\max_i X_i]$ on every instance, improving the $1 - 1/e \approx 0.632$ guarantee.

## Proof sketch

Correa, Saona and Ziliotto lower-bound the performance of every blind strategy by a functional of $\alpha$ that is independent of the instance, using the fact that random arrival times make the events of exceeding the quantile threshold behave like independent Poisson clocks; numerically optimizing $\alpha$ over a class of piecewise functions gives $0.669$.

## Depends on

- [Gambler-to-prophet ratios under different arrival models](prophet-ratio-by-arrival-model.md)

## Sources

- José Correa, Raimundo Saona, Bruno Ziliotto, "Prophet Secretary Through Blind Strategies", Mathematical Programming 190 (2021); SODA (2019), arXiv:1807.07483.
