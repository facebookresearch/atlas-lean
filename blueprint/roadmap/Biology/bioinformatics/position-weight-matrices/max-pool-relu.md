# Bias and ReLU commute with max pooling

For every filter $W$, sequence $x$, $m$ and real $\beta$,

$$\max_{0 \le i \le m} \max\bigl(\mathrm{conv}_W(x, i) + \beta,\ 0\bigr) = \max\bigl(M + \beta,\ 0\bigr),$$

where $M$ is the [max-pooled output](max-pool.md).
