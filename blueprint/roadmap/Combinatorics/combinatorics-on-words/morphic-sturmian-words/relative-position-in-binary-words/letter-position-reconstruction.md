# Reconstruction of a binary word from its relative position function

Let $w$ be an
infinite binary word over $\{a, b\}$ in which both letters occur infinitely often, let $p_a(n)$
and $p_b(n)$ be the positions (counted from $0$) of the $n$-th $a$ and the $n$-th $b$ in $w$, and
let $r(n) = p_b(n) - p_a(n)$. If $r(1) > 0$ then $p_a(1) = 0$ and $p_b(1) = r(1)$; if $r(1) < 0$
then $p_a(1) = -r(1)$ and $p_b(1) = 0$. For every $n \ge 1$, let $k_{n+1}$ be the least natural
number different from all of $p_a(1), \dots, p_a(n), p_b(1), \dots, p_b(n)$. If $r(n+1) > 0$ then
$p_a(n+1) = k_{n+1}$ and $p_b(n+1) = k_{n+1} + r(n+1)$; if $r(n+1) < 0$ then
$p_a(n+1) = k_{n+1} - r(n+1)$ and $p_b(n+1) = k_{n+1}$.

The paper states this as an algorithm; here its output is stated as equalities with the true
positions. Since $r(1) \ne 0$, the paper's "otherwise" in the first step is the case $r(1) < 0$.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 6 (`jis-2025-25.1.5-lem-6`).
