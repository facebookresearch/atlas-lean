# Squared correlation of case status and genotype score

For a [case-control genotype table](total.md) $r, s$ with total $N$, $R = \sum_i r_i$ cases, pooled counts $n_i = r_i + s_i$ and [pooled score variance](score-var.md) $\mathrm{Var}$, put

$$\rho^2 = \frac{\Bigl(\frac{1}{N}\sum_i i\, r_i - \frac{R}{N} \cdot \frac{1}{N}\sum_i i\, n_i\Bigr)^2}{\Bigl(\frac{R}{N} - \bigl(\frac{R}{N}\bigr)^2\Bigr) \mathrm{Var}},$$

with the convention $x/0 = 0$. When the counts are nonnegative, $0 < R < N$ and $\mathrm{Var} > 0$, it is the squared sample correlation of case status ($1$ for cases, $0$ for controls) and genotype score over the $N$ individuals of the table. When the denominator is $0$ the value $0$ is only the convention; for other signed tables the ratio is defined but is not a squared correlation.
