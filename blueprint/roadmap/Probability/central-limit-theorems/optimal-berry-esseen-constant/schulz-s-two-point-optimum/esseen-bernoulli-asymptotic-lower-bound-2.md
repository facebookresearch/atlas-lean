# Esseen's asymptotic lower bound for a two-point law

For a probability measure $\mu$ on
$\mathbb{R}$ and an integer $n \ge 1$, let $F_n$ be the distribution function of
$(X_1 + \dots + X_n)/\sqrt{n}$ for independent random variables $X_1, X_2, \dots$ each with law
$\mu$, let $\Delta_n(\mu) = \sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)|$, where $\Phi$ is the
standard normal distribution function, let $\beta_3(\mu) = \int |x|^3 \, d\mu$, and let
$C_E = (\sqrt{10} + 3)/(6\sqrt{2\pi})$. There is a probability measure $\mu$ on $\mathbb{R}$ with
mean $0$ and variance $1$ that is concentrated on two distinct points, such that for every real
$\varepsilon > 0$ and every $N \in \mathbb{N}$ there is a positive integer $n \ge N$ with

$$\Delta_n(\mu) \ge \frac{(C_E - \varepsilon)\,\beta_3(\mu)}{\sqrt{n}}.$$

In other words, $\limsup_{n \to \infty} \sqrt{n}\,\Delta_n(\mu) / \beta_3(\mu) \ge C_E$.

## Sources

- catalogue C19a, the asymptotic normalized Bernoulli lower-row clause.
