# Eventually linear relative position functions with positive slope

Let $k \ge 1$, $q$
and $c$ be integers with $0 \le c \le k - 1$, and put $j = qk - c$. Let $w$ be an infinite word
over $\{a, b\}$ that starts with $a$ and is a fixed point of the Pisa substitution
$\sigma_{k-c,c,1}$, given by $a \mapsto a^{k-c} b a^c$ and $b \mapsto a$. For an infinite word $v$
write $r_v$ for its relative position function, and let $D$ be the deletion operator, which
deletes the first $b$ and then the first $a$ of a word. (a) If $q \ge 0$, then
$r_{D^q(w)}(n) = kn + j$ for all sufficiently large $n$. (b) If $q < 0$, then for every finite
word $u$ over $\{a, b\}$ of length $-2q$ in which $a$ and $b$ occur equally often (an
equilibrious word), $r_{uw}(n) = kn + j$ for all sufficiently large $n$.

The paper takes $w$ to be the fixed point of $\sigma_{1,k-1,1}$ for every $c$, which is false
unless $c = k - 1$: for $k = 2$ and $j = 2$ ($q = 1$, $c = 0$) that fixed point has
$r_{D(w)}(n) = 2n + 1$ (Theorem 64(c)), not $2n + 2$. The substitution $\sigma_{k-c,c,1}$ is the
one Theorem 64(b) provides ($r_w(n) = kn - c$), from which $D$ (with $r_{D(w)}(n) = r_w(n+1)$
for words that start with $ab$ or $ba$ and contain both letters infinitely often) and
equilibrious prefixes (Lemma 22) shift the index by $q$, giving every progression $kn + j$ with
$k \ge 1$; for $c = k - 1$ it is the paper's $\sigma_{1,k-1,1}$. The paper writes $k \ge 0$, but
the range $0 \le c \le k - 1$ is then empty.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 65 (`jis-2025-25.1.5-prop-65`).
