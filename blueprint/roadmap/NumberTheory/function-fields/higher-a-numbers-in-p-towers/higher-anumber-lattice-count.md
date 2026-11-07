# The lattice-point count of Theorem 1

For natural numbers $p$, $d$, $r$ and $n$, put
$\tau = (p + 1)/d$, $\gamma = ((p - 1) r + (p + 1))/d$ and $t_n = \lfloor \gamma^{-1} p^n \rfloor$
(a floor in $\mathbb{N}$, so $0$ for negative arguments), with the convention that division by
$0$ gives $0$; thus $\tau = \gamma = 0$ when $d = 0$, and $t_n = 0$ when $\gamma = 0$. For a
rational $x$ and an integer $k$ let $[p^k](x) = \lfloor x / p^k \rfloor \bmod p$, the base-$p$
digit of $x$ at $p^k$ when $p \ge 2$ (reduction mod $0$ is the identity). Let $\mu(i)$ be the
lattice boundary of Definition 1: $\mu(i) = \lfloor \tau i \rfloor$ if the sequence
$([p^k](\tau i))_{k \ge 0}$ is lexicographically larger than the sequence
$([p^{-1-k}](\tau i))_{k \ge 0}$, and $\mu(i) = \lceil \tau i \rceil$ otherwise. Let $\Delta_n$
be the set of pairs of integers $(i, j)$ with $t_n < i \le p^n$, $1 \le j \le p^n - 1$ and
$\mu(i) \le j$. The lattice-point count is the rational number
$r (p - 1) t_n (t_n + 1)/(2d) + |\Delta_n|$ (which is $|\Delta_n|$ when $d = 0$).

Theorem 1 (Booher, Cais, Kramer-Miller, Upton) identifies it with the higher $a$-number
$a^r(X_n)$ of a $\mathbb{Z}_p$-tower with minimal break ratios and ramification invariant
$d \mid p - 1$. Bounding $i$ by $p^n$ loses nothing when $\tau \ge 1$, since then
$\mu(i) \ge \lfloor \tau i \rfloor \ge i$.

## Sources

- Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Definition 2 and Theorem 1.
