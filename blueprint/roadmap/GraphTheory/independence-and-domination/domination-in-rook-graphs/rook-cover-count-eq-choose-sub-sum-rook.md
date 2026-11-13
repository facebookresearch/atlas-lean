# Recursion for rook placements covering all rows and columns

For natural numbers
$n, m \ge 1$ and $k$, let $E_{a,b}(k)$ denote the number of $k$-element sets of cells of the
$a \times b$ board that contain a cell in every row and a cell in every column. Then

$$E_{n,m}(k) = \binom{nm}{k} -
\sum_{(r,c) \ne (0,0)} \binom{n}{r} \binom{m}{c} E_{n-r,m-c}(k),$$

where the sum runs over all pairs $(r, c) \ne (0, 0)$ with $0 \le r \le n$ and $0 \le c \le m$.

## Sources

- Stephan Mertens, "Domination Polynomial of the Rook Graph", Theorem 2 (`thm:E-recursion`).
