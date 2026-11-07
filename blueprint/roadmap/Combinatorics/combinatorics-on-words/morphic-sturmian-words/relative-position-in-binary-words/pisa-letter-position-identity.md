# Position identities for the extended Pisa substitution

Let $k \ge 1$, $l \ge 0$ and
$m \ge 1$ be natural numbers, let $\sigma$ be the substitution $a \mapsto a^k b a^l$,
$b \mapsto a^m$, and let $w$ be a one-sided fixed point of $\sigma$ (so $\sigma(w) = w$) that
begins with $a$. For an infinite word $v$ over $\{a, b\}$ and $n \ge 1$, let $p_a(n)$ and
$p_b(n)$ be the positions (counted from $0$) of the $n$-th $a$ and the $n$-th $b$ in $v$, and let
$r(n) = p_b(n) - p_a(n)$. Then for $v = w$ and every $n \ge 1$,

$$p_b(n) = m\,p_a(n) + (k + l + 1 - m)n + m - l - 1$$

and

$$r(n) = (m - 1)p_a(n) + (k + l + 1 - m)n + m - l - 1.$$

Moreover, every infinite word $v$ over $\{a, b\}$ in which both letters occur infinitely often
and whose functions $r$ and $p_a$ satisfy the second identity for all $n \ge 1$ equals $w$.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 57 (`jis-2025-25.1.5-thm-57`).
