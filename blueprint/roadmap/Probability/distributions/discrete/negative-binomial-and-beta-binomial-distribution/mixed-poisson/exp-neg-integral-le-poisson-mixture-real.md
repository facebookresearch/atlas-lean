# Zero inflation by mixing

Let $\nu$ be a probability measure on $\mathbb{R}$ concentrated on $[0, \infty)$ with
$\int |r|\, d\nu < \infty$, and let $p_\nu$ be the [mixed Poisson mass function](poisson-mixture-real.md).
Then

$$p_\nu(0) = \mathbb E\, e^{-\Lambda} \ge e^{-\mathbb E \Lambda},$$

the zero class of the Poisson law with the same mean ($\Lambda \sim \nu$). This is Jensen's
inequality for $\lambda \mapsto e^{-\lambda}$.
