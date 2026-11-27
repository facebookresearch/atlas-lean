# Rényi divergence and Rényi differential privacy

For discrete distributions $P, Q$ and an order $\alpha > 1$, the *Rényi divergence* is

$$
D_\alpha(P \Vert Q) = \frac{1}{\alpha - 1}\log \sum_r P(r)^{\alpha} Q(r)^{1-\alpha} = \frac{1}{\alpha-1}\log \mathbb{E}_{r \sim P}\Bigl[\bigl(P(r)/Q(r)\bigr)^{\alpha-1}\Bigr],
$$

where the sum $\sum_r P(r)(P(r)/Q(r))^{\alpha-1}$ is the order-$\alpha$ *Rényi moment*, the moment generating function of the privacy-loss random variable $\log(P(r)/Q(r))$ at $\alpha - 1$. A mechanism $M$ satisfies *$(\alpha, \varepsilon)$-Rényi differential privacy* (RDP) with respect to an adjacency relation if $D_\alpha(M(x) \Vert M(y)) \le \varepsilon$ for all adjacent $x, y$.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)

## Sources

- Ilya Mironov, "Rényi Differential Privacy", 2017 IEEE 30th Computer Security Foundations Symposium (CSF), 2017.
