# Mean-field lower bound for $\theta(p)$ from a differential inequality

Let $d \in \mathbb{N}$, and for $p \in [0, 1]$ and $n \in \mathbb{N}$ let $\theta_n(p) = \mathbb{P}_p(0 \leftrightarrow \mathbb{Z}^d \setminus \Lambda_{n-1})$ be the [one-arm probability](../exponential-decay-below-the-critical-point/cross-prob.md) and $\theta(p)$ the [percolation probability](../../phase-transition/percolation-probability-and-critical-point/theta.md) of Bernoulli bond percolation on $\mathbb{Z}^d$. Let $0 < p_0 < 1$, let $p \in [p_0, 1)$, and let $f_n : \mathbb{R} \to \mathbb{R}$, $n \in \mathbb{N}$, be functions such that for every $n$:

- $f_n(p) = \theta_n(p)$;
- $f_n$ is differentiable at every $q \in [p_0, 1)$;
- $f_n'(q) \ge \dfrac{1 - f_n(q)}{q(1 - q)}$ for every $q \in (p_0, 1)$;
- $f_n(p_0) \ge 0$.

If $\theta_n(p) \to \theta(p)$ as $n \to \infty$, then

$$\theta(p) \ge \frac{p - p_0}{p(1 - p_0)}.$$

## Sources

- Hugo Duminil-Copin and Vincent Tassion, *A new proof of the sharpness of the phase transition for Bernoulli percolation and the Ising model*, Comm. Math. Phys. 343 (2016), no. 2, 725–745, DOI 10.1007/s00220-015-2480-z.
