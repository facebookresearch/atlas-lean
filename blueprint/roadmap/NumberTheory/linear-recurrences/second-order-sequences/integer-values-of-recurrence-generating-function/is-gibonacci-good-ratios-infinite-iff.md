# Good consecutive ratios of a Gibonacci sequence

Let $p$ and $q$ be coprime integers,
let $(H_n)_{n \ge 0}$ be the Gibonacci sequence with $H_0 = p$ and $H_1 = q$, and put
$m = |q^2 - pq - p^2|$. Call a pair of integers $(a, b)$ admissible when $H_n / H_{n+1}$ is
good for $(a, b)$ for every natural number $n$ with $H_{n+1} \ne 0$. Then there are infinitely
many admissible pairs, and a pair $(a, b)$ is admissible if and only if there are integers $u$
and $v$ with $(q - p) u \equiv 1$, $p v \equiv 1$, $a \equiv -b p u$ and
$a \equiv -b q v \pmod{m}$.

In the source's notation, with modular inverses, the condition reads
$a \equiv -bp(q - p)^{-1} \equiv -bqp^{-1} \pmod{m}$. The source indexes $H$ by all integers.

## Sources

- Knapp, *Fibonacci Generating Functions*, Journal of Integer Sequences 27 (2024), Article 24.3.1, Theorem 3 (`jis-2024-24.3.1-thm-3`).
