# The total merger rate in closed form

Let $\Lambda$ be a finite measure on $[0, 1]$. For every natural number $b$, its [total merger rate](total-merger-rate.md) is

$$\lambda_b = \binom{b}{2} \Lambda(\{0\}) + \int_{(0,1]} \frac{1 - (1 - x)^{b} - b\,x\,(1 - x)^{b-1}}{x^2} \, \Lambda(dx),$$

where $b - 1$ is read as $0$ when $b = 0$. The atom of $\Lambda$ at $0$, which contributes the binary mergers of Kingman's coalescent, is split off, so the integrand is only evaluated where $x > 0$.
