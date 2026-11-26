# Recurrence for the negative-positive numbers

For every triangular recurrence with
parameters $(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$ and all integers $n \le -2$ and
$k \ge 1$, the negative-positive numbers satisfy

$$
a^{NP}_{n,k} = \frac{a^{NP}_{n+1,k} - (\alpha'(n+1) + \beta' k + \gamma')\, a^{NP}_{n,k-1}}
  {\alpha(n+1) + \beta k + \gamma},
$$

where the division is in $\mathbb{Q}$ and division by $0$ gives $0$.

## Sources

- Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Definition 1.
