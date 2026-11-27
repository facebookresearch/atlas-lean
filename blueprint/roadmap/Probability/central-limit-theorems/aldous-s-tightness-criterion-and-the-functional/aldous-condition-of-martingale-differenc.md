# Martingale difference arrays satisfy Aldous's condition

On a probability space, let $(\xi_{n,i})_{n,i \in \mathbb{N}}$ be a triangular array and, for each row $n$, $(\mathcal F_{n,i})_i$ a filtration, such that each $\xi_{n,i}$ is strongly $\mathcal F_{n,i+1}$-measurable and square integrable and $\mathbb{E}[\xi_{n,i} \mid \mathcal F_{n,i}] = 0$ almost surely. If for every $t \in [0, 1]$ the predictable quadratic variation $\sum_{j < \lfloor n t\rfloor} \mathbb{E}[\xi_{n,j}^2 \mid \mathcal F_{n,j}]$ converges in probability to $t$ as $n \to \infty$, then the partial sums of the rows satisfy Aldous's condition.

## Sources

- J. Jacod and A. N. Shiryaev, *Limit Theorems for Stochastic Processes*, 2nd ed., Springer (2003), Theorem VI.4.13 (Rebolledo's criterion), via Lenglart's inequality. Here the limit of the quadratic variation is the continuous deterministic function $t$, and pointwise convergence gives uniform control over windows because the quadratic variation is nondecreasing.
