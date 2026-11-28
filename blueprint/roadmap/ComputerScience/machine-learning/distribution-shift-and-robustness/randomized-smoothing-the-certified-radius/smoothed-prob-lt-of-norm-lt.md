# Certified l2 radius of randomized smoothing

Let $\iota$ be a finite index type, $Y$ a measurable space in which singletons are measurable, $f : \mathbb{R}^\iota \to Y$ a measurable base classifier and $\sigma > 0$. For $x \in \mathbb{R}^\iota$ and a class $c$ write $p_c(x) = \Pr_{Z \sim \mathcal{N}(0, I)}[f(x + \sigma Z) = c]$. Let $\Phi$ be the standard normal distribution function and $\Phi^{-1}$ its quantile function. Suppose $p_A, p_B \in (0, 1)$, a class $a$ satisfies $p_A \le p_a(x)$, and every class $c \ne a$ satisfies $p_c(x) \le p_B$. Then for every $\delta \in \mathbb{R}^\iota$ with

$$\|\delta\| < \frac{\sigma}{2}\,\big(\Phi^{-1}(p_A) - \Phi^{-1}(p_B)\big)$$

and every class $c \ne a$,

$$p_c(x + \delta) < p_a(x + \delta),$$

so the smoothed classifier still predicts $a$ at $x + \delta$.

## Sources

J. Cohen, E. Rosenfeld and J. Z. Kolter, *Certified adversarial robustness via randomized smoothing*, ICML 2019, Theorem 1 (arXiv:1902.02918).
