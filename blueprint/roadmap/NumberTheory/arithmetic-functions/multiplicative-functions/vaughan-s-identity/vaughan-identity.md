# Vaughan's identity

Let $R$ be a commutative ring, let $\mu$ and $\Lambda$ be arithmetic
functions with values in $R$ (so $\mu(0) = \Lambda(0) = 0$), and let $L : \mathbb{N} \to R$ be
any function. Suppose that for every natural number $m$, $\sum_{d \mid m} \mu(d)$ is $1$ if
$m = 1$ and $0$ otherwise, and $\Lambda(m) = \sum_{d \mid m} \mu(d) \, L(m/d)$, where both sums
run over the $d$ with $0 \le d \le m$ and $d \mid m$. Then for all natural numbers $U \ge 1$,
$V \ge 1$ and $n > V$,

$$\Lambda(n) = \sum_{b \mid n,\ b \le U} \mu(b) \, L(n/b) -
\sum_{b \mid n,\ b \le U} \ \sum_{c \le V,\ bc \mid n} \mu(b) \, \Lambda(c) +
\sum_{b \mid n,\ b > U} \ \sum_{c > V,\ bc \mid n} \mu(b) \, \Lambda(c),$$

where $b$ and $c$ range over $0, 1, \dots, n$.

When $R = \mathbb{R}$, $\mu$ is the Möbius function, $L = \log$ and $\Lambda$ is the von Mangoldt
function, the hypotheses hold and this is the classical Vaughan identity.

## Sources

- https://en.wikipedia.org/wiki/Vaughan%27s_identity It follows from `vaughan_identity_general`; the hypotheses `hU` and `hV` are unused and keep the source's shape.
