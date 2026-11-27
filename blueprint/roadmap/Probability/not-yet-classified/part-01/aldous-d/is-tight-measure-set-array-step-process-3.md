# Tightness in `D([0,1])` of martingale difference arrays

On a probability space, let each row $(\xi_{n,i})_i$ be adapted to a filtration $(\mathcal F_{n,i})_i$ ($\xi_{n,i}$ is $\mathcal F_{n,i+1}$-measurable), square integrable, with $E[\xi_{n,i} \mid \mathcal F_{n,i}] = 0$. Suppose that for every $t \in [0,1]$ the predictable quadratic variation $\sum_{j < \lfloor n t \rfloor} E[\xi_{n,j}^2 \mid \mathcal F_{n,j}]$ converges in probability to $t$, and the Lindeberg condition holds: $\sum_{k<n} E[\xi_{n,k}^2 \mathbf 1\{|\xi_{n,k}| > \varepsilon\}] \to 0$ for every $\varepsilon > 0$. Then the laws of the step processes $t \mapsto \sum_{i < \lfloor n t \rfloor} \xi_{n,i}$ are tight in $D([0,1])$ with the J1 topology.

## Sources

- J. Jacod and A. N. Shiryaev, *Limit Theorems for Stochastic Processes*, 2nd ed., Springer, 2003, Theorem VI.4.13 (Rebolledo: the quadratic-variation condition gives Aldous's condition) with Theorem VI.4.5.
