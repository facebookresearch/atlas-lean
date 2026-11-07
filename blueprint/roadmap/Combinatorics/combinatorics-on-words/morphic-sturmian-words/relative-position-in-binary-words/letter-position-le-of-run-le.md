# Bounds on position functions for words with bounded runs

Let $w$ be an infinite binary
word over $\{a, b\}$ that starts with $a$ and in which both letters occur infinitely often, and
let $c \ge 0$ be an integer such that every block of consecutive equal letters of $w$ has length
at most $c$. Write $p_\alpha(n)$ for the position (counted from $0$) of the $n$-th occurrence of
the letter $\alpha$ in $w$, and $r(n) = p_b(n) - p_a(n)$. Then for every $n \ge 1$,
$p_a(n) \le (c+1)(n-1)$, $p_b(n) \le (c+1)n - 1$ and $c(1-n) + 1 \le r(n) \le cn$.

The paper prints the lower bound $(1-c)n + 1 \le r(n)$, which is false: for $w = (abb)^\omega$
and $c = 2$, $r(4) = 5 - 9 = -4 < -3$. The bound $c(1-n) + 1$ is the one derived in the paper's
proof. Stating the result for every bound $c$ of the runs is equivalent to stating it for the
longest run.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 25 (`jis-2025-25.1.5-lem-25`).
