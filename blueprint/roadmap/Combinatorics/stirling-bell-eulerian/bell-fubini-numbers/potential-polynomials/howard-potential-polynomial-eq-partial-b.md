# Howard's formula for potential polynomials

Let $K$ be a field of characteristic zero,
let $r \ge 1$ and $n$ be natural numbers, and let $a_0, a_1, a_2, \dots$ be a sequence in $K$
with $a_r \ne 0$. Let $g$ be the formal power series

$$g(x) = \sum_{k \ge 0} \frac{r!\, a_{r+k}}{a_r\, (r+k)!}\, x^k,$$

let $g^{-1}$ be its inverse in $K[[x]]$, and write $[x^n]\, f$ for the coefficient of $x^n$ in a
power series $f$. Let $P \in K[X]$ be a polynomial of degree at most $n$ such that
$P(m) = n!\, [x^n]\, (g^{-1})^m$ for every natural number $m \le n$. Then

$$P(X) = \sum_{i=0}^{n} (-1)^i \left(\frac{r!}{a_r}\right)^i \frac{n!\, i!}{(n+ri)!} \cdot
\frac{X(X+1)\cdots(X+i-1)}{i!} \cdot \frac{(X+n)(X+n-1)\cdots(X+i+1)}{(n-i)!} \cdot
B_{n+ri,\,i}(\tilde a),$$

where empty products equal $1$, $B_{n+ri,\,i}$ is the partial Bell polynomial, and $\tilde a$
is the sequence with $\tilde a_j = a_j$ for $j \ge r$ and $\tilde a_j = 0$ for $j < r$.

## Sources

- G. Nemes, Journal of Integer Sequences 13 (2010), https://cs.uwaterloo.ca/journals/JIS/VOL13/Nemes/nemes2.tex, lines 120-133 (generic) and 166-173 (specialization).
