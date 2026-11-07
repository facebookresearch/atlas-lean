# Relative position of iterated deletions of the Fibonacci word

Let
$f = abaababaabaab\cdots$ be the Fibonacci word, the fixed point of $a \mapsto ab$,
$b \mapsto a$. Let $D$ be the operator on infinite words over $\{a, b\}$ that deletes the first
$b$ and then the first $a$ of the result, and for such a word $v$ let
$r_v(n) = p_b(n) - p_a(n)$, where $p_a(n)$ and $p_b(n)$ are the positions of the $n$-th $a$ and
the $n$-th $b$ in $v$. Then for every natural number $k$ there is an $N$ such that
$r_{D^k(f)}(n) = n + k$ for all $n > N$.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 44 (`jis-2025-25.1.5-thm-44`).
