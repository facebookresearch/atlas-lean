# Base-$b$ generalized digital binomial theorem

Let $b \ge 2$, let $N$ and $n$ be natural
numbers with $n < b^N$, and let $x$ and $y$ be real numbers. For a natural number $m$ write
$m_i = \lfloor m / b^i \rfloor \bmod b$ for its $i$-th base-$b$ digit, and write
$z^{\overline{j}} = z(z+1)\cdots(z+j-1)$ for the rising factorial. Then

$$\prod_{i=0}^{N-1} \frac{(x+y)^{\overline{n_i}}}{n_i!} = \sum_{m} \left(\prod_{i=0}^{N-1}
\frac{x^{\overline{m_i}}}{m_i!}\right) \left(\prod_{i=0}^{N-1}
\frac{y^{\overline{(n-m)_i}}}{(n-m)_i!}\right),$$

where the sum runs over the natural numbers $m \le n$ with $m_i \le n_i$ for every $i < N$.

## Sources

- Hieu D. Nguyen, "A Generalization of the Digital Binomial Theorem," Journal of Integer Sequences 18 (2015), Article 15.5.7, Theorem (label th:digital-binomial-theorem-non-binary), equation (eq:digital-binomial-theorem-non-binary), lines 122–127, https://cs.uwaterloo.ca/journals/JIS/VOL18/Nguyen/nguyen6.tex
