# Closed formula for hook tableau counts

For natural numbers $n$ and $k$ with
$k + 2 \le n$, let $\mathrm{SYT}_k(2,1;n)$ be the number of standard Young tableaux of order $n$
in the $(2,1)$-hook whose first row is longer than its second row by exactly $k$. Then, as an
identity of rational numbers,

$$
\mathrm{SYT}_k(2,1;n) = (-1)^{n+k} + \sum_{i=0}^{\lfloor (n-k-1)/2 \rfloor}
\sum_{\substack{0 \le j \le n-k-1-2i \\ j \equiv n+k-1 \pmod 2}}
\frac{2k+2}{n+k+1-2i-j} \binom{n-2i-2}{j} \binom{n-2i-j-1}{\frac{n+k-j-1}{2} - i}.
$$

When $k = 0$ and $2i = n - 1$, the upper argument $n - 2i - 2$ would be $-1$; it is read as $0$,
so the only term of that inner sum, $j = 0$, has binomial factor $\binom{0}{0} = 1$.

## Sources

- Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal of Integer Sequences 28 (2025), Article 25.8.1, Theorem 2 (`jis-2025-25.8.1-thm-2`).
