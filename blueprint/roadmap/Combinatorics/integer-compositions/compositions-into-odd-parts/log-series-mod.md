# Logarithmic series over a residue class

For natural numbers $m$ and $s$, $L_{m,s}(y)$ is the formal power series over $\mathbb{Q}$

$$L_{m,s}(y) = \sum_{\substack{r \ge 1 \\ r \bmod m \,=\, s \bmod m}} \frac{y^r}{r},$$

with $r \bmod 0 = r$, so $L_{0,s}(y) = y^s / s$ for $s \ge 1$ and $L_{0,0} = 0$. Only $s \bmod m$ matters. For $m \ge 1$, $L_{m,0}(y) = \sum_{k \ge 1} y^{km}/(km)$ is the expansion of $\frac{1}{m} \log \frac{1}{1 - y^m}$, and for $1 \le s \le m - 1$, $L_{m,s}(y) = \sum_{k \ge 0} y^{s+km}/(s+km)$ is the expansion of $\int_0^y \frac{u^{s-1}}{1 - u^m}\, du$.

## Sources

- Joshua P. Bowman, *Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, remark after Theorem 3.
