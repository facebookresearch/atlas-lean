# Even-binomial-type sums are Dold realizable

Let $r \ge 1$, $s$, $t$ and $u$ be natural
numbers with $t + u \ge 1$, and let

$$T(n) = \sum_{k=0}^{n} \binom{n}{2k}^r \binom{n+k}{k}^s \binom{2k}{k}^t \binom{2(n-k)}{n-k}^u.$$

Then the integer sequence $(T(n))_{n \ge 0}$ is Dold realizable.

The hypothesis $t + u \ge 1$ is added to the source: for $t = u = 0$ the Möbius transform at
$n = 2$ is $T(2) - T(1) = 3^s$, which is odd, so the sequence is not Dold realizable.

## Sources

- Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer Sequences 27 (2024), Article 24.3.3, Theorem 18 (`jis-2024-24.3.3-thm-18`).
