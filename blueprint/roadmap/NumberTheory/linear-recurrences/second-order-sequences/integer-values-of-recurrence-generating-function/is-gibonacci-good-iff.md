# Congruence criterion for good fractions

Let $a, b, p, q$ be integers with
$(a, b) \ne (0, 0)$, $q \ne 0$ and $\gcd(p, q) = 1$, and put $m = |q^2 - pq - p^2|$. Then
$p / q$ is good for $(a, b)$ if and only if there are integers $u$ and $v$ with
$(q - p) u \equiv 1$, $p v \equiv 1$, $a \equiv -b p u$ and $a \equiv -b q v \pmod{m}$.

In the source's notation, with modular inverses, the condition reads
$a \equiv -bp(q - p)^{-1} \equiv -bqp^{-1} \pmod{m}$.

## Sources

- Knapp, *Fibonacci Generating Functions*, Journal of Integer Sequences 27 (2024), Article 24.3.1, Lemma 6 (`jis-2024-24.3.1-lem-6`).
