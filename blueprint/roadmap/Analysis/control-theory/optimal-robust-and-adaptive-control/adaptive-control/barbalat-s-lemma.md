# Barbălat's lemma

If $\phi : [0, \infty) \to \mathbb{R}$ is uniformly continuous and $\lim_{t \to \infty}\int_0^t \phi(s)\, ds$ exists and is finite, then $\phi(t) \to 0$ as $t \to \infty$.

**Proof.** Suppose $|\phi(t_k)| \ge \varepsilon$ along $t_k \to \infty$. Uniform continuity gives $\delta > 0$ with $|\phi(t) - \phi(t_k)| < \varepsilon/2$ for $|t - t_k| \le \delta$, so $\phi$ keeps the sign of $\phi(t_k)$ there and $\big|\int_{t_k}^{t_k + \delta}\phi\big| \ge \varepsilon\delta/2$, which contradicts the Cauchy criterion for the convergent integral.

## Sources

- B. Farkas and S.-A. Wegner, "Variations on Barbălat's lemma", *American Mathematical Monthly* 123(8), 2016, <https://arxiv.org/abs/1411.1611>, Theorem 1 (Barbălat's lemma, a uniformly continuous function with a convergent improper integral tends to $0$).
