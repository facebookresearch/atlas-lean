# The sample mean maximizes the normal likelihood with known variance

Let $n \ge 1$, let $x_1, \dots, x_n$ be real observations and let $\sigma^2 > 0$ be known. For i.i.d. $N(\mu, \sigma^2)$ observations the likelihood is $L(\mu) = \prod_i (2\pi\sigma^2)^{-1/2}\exp(-(x_i - \mu)^2/(2\sigma^2))$, and it has the unique maximizer $\mu = \bar x$. Proof: $\sum_i (x_i - \mu)^2 = \sum_i (x_i - \bar x)^2 + n(\bar x - \mu)^2$, so $\log L(\mu)$ is a constant minus $n(\bar x - \mu)^2/(2\sigma^2)$.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
