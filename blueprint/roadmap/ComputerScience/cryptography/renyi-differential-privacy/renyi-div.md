# Rényi divergence

For probability mass functions $P, Q$ on a finite type and $\alpha \in \mathbb{R}$, the formal Rényi divergence $D_\alpha(P \| Q)$ is an extended real: if $P$ has [support inside](support.md) that of $Q$ and $\alpha > 1$, it is the [real Rényi divergence](renyi-div-real.md)

$$
\frac{1}{\alpha-1} \log \sum_{w \,:\, Q(w) > 0} \frac{P(w)^{\alpha}}{Q(w)^{\alpha-1}};
$$

otherwise it is $+\infty$. This is the convention of the formalization, not the standard Rényi divergence at small orders: Mironov's Definition 3 takes the order-one divergence to be the Kullback–Leibler divergence, so that $D_1(P \| P) = 0$, whereas here $D_\alpha = +\infty$ for every $\alpha \le 1$. Only orders $\alpha > 1$ are used for Rényi differential privacy.

## Sources

- I. Mironov, *Rényi Differential Privacy*, IEEE Computer Security Foundations Symposium (CSF), 2017.
