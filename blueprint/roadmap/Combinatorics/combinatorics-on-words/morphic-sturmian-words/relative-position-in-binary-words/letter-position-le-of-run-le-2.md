# Linear bounds for words with bounded runs

Let $w$ be an infinite binary word over the
letters $a$ and $b$ in which both letters occur infinitely often, and let $c$ be a natural number
such that every block of consecutive equal letters of $w$ has length at most $c$. Let $p_a(n)$
and $p_b(n)$ be the positions (counting from $0$) of the $n$-th $a$ and the $n$-th $b$ in $w$, and
let $r(n) = p_b(n) - p_a(n)$. Then for every $n \ge 1$, $p_a(n) \le (c+1)n - 1$,
$p_b(n) \le (c+1)n - 1$ and $-cn \le r(n) \le cn$.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 27 (`jis-2025-25.1.5-cor-27`).
