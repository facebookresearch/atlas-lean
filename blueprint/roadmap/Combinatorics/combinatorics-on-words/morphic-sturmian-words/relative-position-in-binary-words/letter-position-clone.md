# Position functions of a cloned word

Let $w$ be an infinite binary word over the
letters $a$ and $b$ in which both letters occur infinitely often, let $k$ be a natural number,
and let $\varphi_k(w)$ be the word whose letter at position $i$ is the letter of $w$ at position
$\lfloor i/k \rfloor$ (for $k \ge 1$, the word obtained from $w$ by repeating each letter $k$
times). For a word $v$ and a letter $\alpha$, let $p_{\alpha,v}(n)$ be the position (counting
from $0$) of the $n$-th occurrence of $\alpha$ in $v$, and let $r_v(n) = p_{b,v}(n) - p_{a,v}(n)$.
Then for all natural numbers $m$ and $j$ with $1 \le j \le k$,
$p_{a,\varphi_k(w)}(mk+j) = k\,p_{a,w}(m+1) + j - 1$,
$p_{b,\varphi_k(w)}(mk+j) = k\,p_{b,w}(m+1) + j - 1$ and
$r_{\varphi_k(w)}(mk+j) = k\,r_w(m+1)$.

The paper takes $k \ge 2$; the identities hold for $k = 1$ ($\varphi_1$ is the identity) and are
vacuous for $k = 0$, so no bound on $k$ is assumed.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 24 (`jis-2025-25.1.5-lem-24`).
