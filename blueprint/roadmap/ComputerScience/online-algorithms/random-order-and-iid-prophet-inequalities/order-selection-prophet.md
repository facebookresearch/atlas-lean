# Order-selection prophet inequality with ratio $0.725$

In the order-selection prophet inequality, where the gambler knows the distributions of independent values and chooses the arrival order, there is an order together with a stopping rule achieving $\mathbb{E}[X_\tau] \ge 0.725\,\mathbb{E}[\max_i X_i]$ on every instance, improving on the $0.669$ guarantee of blind strategies for random order and approaching the i.i.d. constant $\beta \approx 0.745$.

## Proof sketch

Peng and Tang reduce order design to choosing an *arrival time* in $[0,1]$ for each variable, with values arriving in increasing order of arrival times, and analyze threshold rules depending on time through a continuous relaxation; optimizing arrival times jointly with thresholds yields a factor-revealing program whose value is at least $0.725$.

## Depends on

- [Gambler-to-prophet ratios under different arrival models](prophet-ratio-by-arrival-model.md)

## Sources

- Bo Peng, Zhihao Gavin Tang, "Order Selection Prophet Inequality: From Threshold Optimization to Arrival Time Design", FOCS (2022); SIAM Journal on Computing (2025), arXiv:2204.01425.
