# Order-selection prophet inequality with ratio $0.725$

In the order-selection prophet inequality, where the gambler knows the distributions of independent values and chooses the arrival order, there is an order together with a stopping rule achieving $\mathbb{E}[X_\tau] \ge 0.725\,\mathbb{E}[\max_i X_i]$ on every instance, improving on the $0.669$ guarantee of blind strategies for random order and approaching the i.i.d. constant $\beta \approx 0.745$.

## Proof sketch

Peng and Tang translate order selection into *arrival time design*: each item draws an arrival time in $[0, 1]$ independently from a distribution $F_i$ chosen by the algorithm, items are presented in increasing order of arrival times, and the gambler accepts the first item whose value exceeds a fixed time-dependent threshold $\tau(t)$, where $\Pr[\max_i X_i > \tau(t)] = t$. They choose the $F_i$ so that $\Pr[\mathrm{ALG} > \tau(t)] \ge \Gamma t$ for every $t$, with $\Gamma = \frac{\ln \alpha + 1}{\ln \alpha + 1 - \alpha} \approx 0.725$ for a constant $\alpha \approx 0.211$ defined by an integral equation, and integrating over $t$ gives the ratio. The arrival times are random, so a fixed order with at least this guarantee exists by averaging.

## Depends on

- [Gambler-to-prophet ratios under different arrival models](prophet-ratio-by-arrival-model.md)

## Sources

- Bo Peng, Zhihao Gavin Tang, "Order Selection Prophet Inequality: From Threshold Optimization to Arrival Time Design", FOCS (2022); SIAM Journal on Computing, arXiv:2204.01425, Lemma 2.1 and Theorem 2.1.
