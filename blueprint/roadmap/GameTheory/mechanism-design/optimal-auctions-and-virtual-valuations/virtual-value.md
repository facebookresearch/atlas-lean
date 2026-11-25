# Virtual valuation

Let $a, b \in \mathbb{R}$ and let $f : \mathbb{R} \to \mathbb{R}$ satisfy $\int_a^b f = 1$, with $F(t) = \int_a^t f$
(oriented integrals, so $a > b$ is allowed). The virtual valuation is

$$\varphi(t) = t - \frac{1 - F(t)}{f(t)} \qquad (t \in \mathbb{R}),$$

with the convention that the quotient is $0$ where $f(t) = 0$, so that $\varphi(t) = t$ there. In the usual
interpretation, $a < b$, $f \ge 0$ on $[a, b]$ is a probability density of values with distribution function
$F$, and $\varphi(t)$ is Myerson's virtual valuation at the values $t \in [a, b]$ with $f(t) > 0$ (Myerson 1981,
(5.1) with zero revision effects).

## Sources

- R. B. Myerson, "Optimal auction design", *Mathematics of Operations Research* 6(1) (1981), 58–73, (5.1), here with zero revision effects `eᵢ = 0`.
