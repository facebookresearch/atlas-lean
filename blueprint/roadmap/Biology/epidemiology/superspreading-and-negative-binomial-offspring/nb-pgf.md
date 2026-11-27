# Negative-binomial probability generating function

For real $R$, $k$ and $s$, the negative-binomial generating function is

$$G_{R,k}(s) = \left(1 + \frac{R}{k}(1 - s)\right)^{-k},$$

with $R/k$ read as $0$ when $k = 0$ (so $G_{R,0}(s) = 1$ for all $R$ and $s$), and with real powers $x^y$ with the conventions $0^0 = 1$, $0^y = 0$ for $y \ne 0$, and $x^y = |x|^y \cos(\pi y)$ for $x < 0$ (so $(-8)^{1/3} = 1$).
For $R \ge 0$, $k > 0$ and $0 \le s \le 1$ it is the probability generating function of the
[negative-binomial offspring law](nb-offspring.md) with mean $R$ and dispersion $k$.
