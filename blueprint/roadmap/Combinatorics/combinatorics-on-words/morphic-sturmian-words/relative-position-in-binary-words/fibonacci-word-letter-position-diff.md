# Position differences in the Fibonacci word

Let $f = \ell_0 \ell_1 \ell_2 \cdots =
abaab\cdots$ be the Fibonacci word, the infinite Fibonacci word with each $0$ written as $a$
and each $1$ as $b$. Let $p_a(n)$ and $p_b(n)$ be the positions (counted from $0$) of the
$n$-th $a$ and the $n$-th $b$ in $f$, and let $r(n) = p_b(n) - p_a(n)$. Then for every $n \ge 1$:
$p_a(n+1) - p_a(n)$ is $2$ if $\ell_{n-1} = a$ and $1$ if $\ell_{n-1} = b$;
$p_b(n+1) - p_b(n)$ is $3$ if $\ell_{n-1} = a$ and $2$ if $\ell_{n-1} = b$; and $r(n) = n$.

The printed statement gives the codings $(1, 2)$ and $(2, 3)$ instead, which are false:
$p_a$ takes the values $0, 2, 3, 5, \ldots$, so $p_a(2) - p_a(1) = 2$ while $f$ starts with
$a$. The codings above are the ones derived in the paper's proof.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 38 (`jis-2025-25.1.5-thm-38`).
