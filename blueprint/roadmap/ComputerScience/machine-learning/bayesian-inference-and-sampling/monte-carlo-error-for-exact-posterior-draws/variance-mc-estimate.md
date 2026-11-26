# Variance of the Monte Carlo estimate

Let $\mu$ be a measure on a measurable space $\Omega$, $\nu$ a measure on a measurable space $\alpha$, and $f : \alpha \to \mathbb{R}$ measurable and square-integrable ($f \in L^2(\nu)$). Let $X_0, X_1, \ldots : \Omega \to \alpha$ be measurable, mutually independent under $\mu$, each with law $\nu$. Then for every $m \ne 0$, the Monte Carlo estimate $\widehat{f}_m = \frac{1}{m}\sum_{i<m} f(X_i)$ has variance

$$\operatorname{Var}_\mu\big(\widehat{f}_m\big) = \frac{\operatorname{Var}_\nu(f)}{m} .$$

## Sources

C. P. Robert and G. Casella, *Monte Carlo Statistical Methods*, 2nd ed., Springer, 2004, Section 3.2.
