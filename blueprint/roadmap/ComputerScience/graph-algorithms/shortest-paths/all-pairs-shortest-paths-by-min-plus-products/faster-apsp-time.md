# Operation counts of FASTER-APSP

Let $\alpha$ be a type with addition, multiplication and
zero, let $W$ be an $n \times n$ matrix over $\alpha$, and let $k = \lceil \log_2 (n - 1) \rceil$ be
the least natural number with $n - 1 \le 2^k$. On input $W$, FASTER-APSP performs exactly
$n^2 + 2 k n^2$ copy and fill assignments, $k n^3$ scalar additions and $k n^3$ scalar
multiplications.

Assignments count the matrix cells copied or filled with zero; the accumulator vector updates
inside the matrix multiplications are not counted.
