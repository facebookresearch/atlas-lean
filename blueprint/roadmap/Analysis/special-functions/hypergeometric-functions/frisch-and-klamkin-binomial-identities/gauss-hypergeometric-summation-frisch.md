# Gauss summation at Frisch's specialization

Let $n \ge 1$ be an integer and let $b$ and
$c$ be real numbers with $c > n$ and $b > -1$. Then

$$
{}_2F_1(1 + b - c, n; b + 1; 1) =
  \frac{\Gamma(c - n)\,\Gamma(b + 1)}{\Gamma(c)\,\Gamma(b - n + 1)},
$$

where ${}_2F_1(\alpha, \beta; \gamma; 1) =
\sum_{k \ge 0} \frac{(\alpha)_k (\beta)_k}{(\gamma)_k\, k!}$ and $(x)_k$ is the rising factorial.

The Gamma function is taken to be $0$ at its poles and division by $0$ gives $0$, so the right
side is $0$ when $b - n + 1$ is a nonpositive integer.

## Sources

- Ulrich Abel, "A Short Proof of the Binomial Identities of Frisch and Klamkin," Journal of Integer Sequences 23 (2020), Article 20.7.1, displayed Frisch specialization at source lines 200-205 of the official TeX `https://cs.uwaterloo.ca/journals/JIS/VOL23/Abel/abel12.tex`.
