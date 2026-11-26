# Trudi's formula for Toeplitz–Hessenberg determinants, general case

Let $R$ be a
commutative ring, let $n \ge 0$, and let $a_0, a_1, a_2, \dots$ be any elements of $R$. Let $A_n$
be the $n \times n$ matrix whose entry in row $i$ and column $j$ ($0 \le i, j < n$) is $a_{i+1-j}$
if $j \le i + 1$ and $0$ otherwise; for $n = 0$ it is the empty matrix, whose determinant is $1$.
Then

$$\det A_n = \sum_{c} (-a_0)^{n - \ell(c)} \, a_{c_1} a_{c_2} \cdots a_{c_{\ell(c)}},$$

where $c = (c_1, \dots, c_{\ell(c)})$ runs over the compositions of $n$, that is, the finite
sequences of positive integers with sum $n$, and $\ell(c)$ is the number of parts of $c$.

No hypothesis $n \ge 1$ or $a_0 \ne 0$ is needed.
