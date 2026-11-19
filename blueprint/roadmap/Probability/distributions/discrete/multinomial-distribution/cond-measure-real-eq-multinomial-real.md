# Poisson conditioning

Let $\iota$ be a finite set and $(X_i)_{i \in \iota}$ mutually independent measurable
$\mathbb{N}$-valued random variables on a measure space $(\Omega, \mu)$ with
$X_i \sim \operatorname{Poisson}(\lambda_i)$, $\lambda_i \ge 0$, and $\sum_i \lambda_i > 0$. Then for
every $N \in \mathbb{N}$ and every count vector $x \in \mathbb{N}^\iota$,

$$\mu\Bigl(X = x \Bigm| \sum_i X_i = N\Bigr) = M_N\Bigl(\frac{\lambda}{\sum_j \lambda_j};\, x\Bigr),$$

where $M_N(p; x)$ is the [multinomial mass function](multinomial-real.md): given their total, the
counts are multinomial with $N$ throws and cell probabilities $\lambda_i / \sum_j \lambda_j$.

## Sources

- N. L. Johnson, S. Kotz and N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley, 1997, Chapter 35.
