# Runs of one letter and gaps between letter positions

Let $w = \ell_0 \ell_1 \ell_2 \cdots$
be an infinite word over the letters $a$ and $b$ in which both letters occur infinitely often and
$\ell_0 = a$. For a letter $\alpha$ and $n \ge 1$, let $p_\alpha(n)$ be the position of the $n$-th
occurrence of $\alpha$ in $w$, counting positions from $0$. Let $k \ge 1$. Then the following are
equivalent: there is $i$ with $\ell_{i+j} = b$ for all $0 \le j < k$ (the block $b^k$ occurs in
$w$); there is $n \ge 1$ with $p_a(n+1) - p_a(n) > k$; and there is $n \ge 1$ with
$p_b(n+j+1) - p_b(n+j) = 1$ for all $0 \le j < k - 1$. Moreover, there is $i$ with
$\ell_{i+j} = a$ for all $0 \le j < k$ (the block $a^k$ occurs in $w$) if and only if there is
$n \ge 1$ with $p_a(n+j+1) - p_a(n+j) = 1$ for all $0 \le j < k - 1$.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 13 (`jis-2025-25.1.5-lem-13`).
