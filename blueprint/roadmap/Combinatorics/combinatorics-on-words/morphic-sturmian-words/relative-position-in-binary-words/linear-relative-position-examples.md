# Words with linear relative position function

For integers $k, l, m \ge 0$ write
$\sigma_{k,l,m}$ for the substitution $a \mapsto a^k b a^l$, $b \mapsto a^m$, and for a binary
word $v$ let $r_v(n) = p_{b,v}(n) - p_{a,v}(n)$, where $p_{\alpha,v}(n)$ is the position (counted
from $0$) of the $n$-th occurrence of the letter $\alpha$ in $v$.
(a) For every $j \ge 1$, the word $v = (a^j b^j)^\omega$ has $r_v(n) = j$ for all $n \ge 1$.
(b) For integers $0 \le j < k$, every fixed point $w$ of $\sigma_{k-j,j,1}$ that starts with $a$
has $r_w(n) = kn - j$ for all $n \ge 1$.
(c) For every $k \ge 1$, if $w$ is a fixed point of $\sigma_{1,k-1,1}$ that starts with $a$ and
$D(w)$ is the word $w$ with its first $a$ and its first $b$ deleted, then $r_{D(w)}(n) = kn + 1$
for all $n \ge 1$.

The paper writes $k \ge 0$ in (c), but $\sigma_{1,k-1,1}$ needs $k \ge 1$.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 64 (`jis-2025-25.1.5-thm-64`).
