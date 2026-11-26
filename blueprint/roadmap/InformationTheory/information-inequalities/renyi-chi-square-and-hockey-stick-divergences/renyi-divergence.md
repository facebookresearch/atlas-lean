# Renyi divergence of discrete distributions

Let $X$ be a countable set, $p, q$ probability distributions on $X$ and $\alpha > 1$. The *Renyi moment* of order $\alpha$ is

$$
M_\alpha(p \,\|\, q) = \sum_{x \in X} p(x) \Big(\frac{p(x)}{q(x)}\Big)^{\alpha - 1} \in [0, \infty],
$$

where a term with $p(x) > 0 = q(x)$ equals $+\infty$ and a term with $p(x) = 0$ equals $0$. The *Renyi divergence* of order $\alpha$, in nats, is

$$
D_\alpha(p \,\|\, q) = \frac{1}{\alpha - 1} \ln M_\alpha(p \,\|\, q) \in [0, \infty],
$$

equal to $+\infty$ when $M_\alpha = +\infty$ (in particular whenever the support of $p$ is not contained in that of $q$). Equivalently $M_\alpha(p\|q) = \sum_x q(x)^{1-\alpha} p(x)^\alpha$ on the support of $q$.

## Sources

- A. Renyi, "On Measures of Entropy and Information", Proceedings of the Fourth Berkeley Symposium on Mathematical Statistics and Probability, Vol. 1, University of California Press, 1961.
- I. Mironov, "Renyi Differential Privacy", IEEE 30th Computer Security Foundations Symposium (CSF), 2017.
