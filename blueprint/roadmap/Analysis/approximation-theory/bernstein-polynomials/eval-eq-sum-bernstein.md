# Values of a polynomial from its Bernstein coefficients

For integers $0 \le \nu \le n$, the Bernstein polynomial is $b_{n,\nu}(s) = \binom{n}{\nu} s^{\nu} (1 - s)^{n - \nu}$, a real polynomial in $s$. Let $p$ be a real polynomial of degree at most $n$ (the zero polynomial included), with degree-$n$ Bernstein coefficients $c_j = \sum_{k=0}^{n} p_k \binom{j}{k} / \binom{n}{k}$, where $p_k$ is the coefficient of $s^k$. Then for every real number $s$, not only for $0 \le s \le 1$,

$$p(s) = \sum_{j=0}^{n} c_j\, b_{n,j}(s).$$
