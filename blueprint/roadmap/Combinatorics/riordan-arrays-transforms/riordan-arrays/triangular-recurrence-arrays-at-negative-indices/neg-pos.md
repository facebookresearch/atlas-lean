# Negative-positive numbers

Let $a_{n,k}$ ($n, k \ge 0$) be the triangular array of a
triangular recurrence with parameters $(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$. Its
negative-positive numbers $a^{NP}_{n,k} \in \mathbb{Q}$, for $n, k \in \mathbb{Z}$, are defined by
$a^{NP}_{n,k} = a_{n,k}$ for $n, k \ge 0$, $a^{NP}_{n,k} = 0$ for $k < 0$, and, for $n < 0 \le k$,
recursively by

$$
a^{NP}_{n,k} = \frac{a^{NP}_{n+1,k} - (\alpha'(n+1) + \beta' k + \gamma')\, a^{NP}_{n,k-1}}
  {\alpha(n+1) + \beta k + \gamma},
$$

where division by $0$ gives $0$.

## Sources

- Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Definition 1.
