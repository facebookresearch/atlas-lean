# Prepending an equilibrious word shifts the position functions

Let $u$ be a finite word
over $\{a, b\}$ of length $2k$ that is equilibrious (it contains as many letters $a$ as letters
$b$), and let $w$ be an infinite binary word in which both letters occur infinitely often. For a
word $v$, write $p_{\alpha,v}(n)$ for the position (counted from $0$) of the $n$-th occurrence of
the letter $\alpha$ in $v$, and $r_v(n) = p_{b,v}(n) - p_{a,v}(n)$. Then for every $n \ge 1$ the
concatenation $uw$ satisfies $p_{a,uw}(n+k) = p_{a,w}(n) + 2k$, $p_{b,uw}(n+k) = p_{b,w}(n) + 2k$
and $r_{uw}(n+k) = r_w(n)$.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 22 (`jis-2025-25.1.5-lem-22`).
