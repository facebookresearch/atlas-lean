# Conditional variance theorem for martingales

Let $(\Omega, \mu)$ be a probability space
with a filtration $(\mathcal{F}_n)_{n \in \mathbb{N}}$, and let $(X_n)_{n \in \mathbb{N}}$ be a
real-valued martingale with respect to $(\mathcal{F}_n)$ and $\mu$ such that $X_n$ is
square-integrable for every $n$. Then for all $m \le n$, almost surely

$$
\mathbb{E}[(X_n - X_m)^2 \mid \mathcal{F}_m] = \mathbb{E}[X_n^2 \mid \mathcal{F}_m] - X_m^2.
$$

This expresses the conditional variance of the increment $X_n - X_m$ in terms of the conditional
second moment of $X_n$.

## Sources

- Lecture 28, conditional variance theorem.
