# Minimum Colless index

Let $\mathcal T_n$ be the set of rooted bifurcating tree shapes with $n$ leaves and let $c_n = \min_{T \in \mathcal T_n} C(T)$ be the minimum [Colless index](colless-index.md).

**Recurrence.** $c_1 = 0$ and, for every $n \ge 2$,

$$c_n = \min\{c_{n_a} + c_{n_b} + n_a - n_b : n_a \ge n_b \ge 1,\ n_a + n_b = n\} = c_{\lceil n/2 \rceil} + c_{\lfloor n/2 \rfloor} + \lceil n/2 \rceil - \lfloor n/2 \rfloor,$$

equivalently $c_{2n} = 2c_n$ and $c_{2n+1} = c_{n+1} + c_n + 1$. The minimum is attained by the **maximally balanced tree** $T^{\mathrm{mb}}_n$, obtained by recursively splitting every set of $m$ descendant leaves into parts of sizes $\lceil m/2 \rceil$ and $\lfloor m/2 \rfloor$: $C(T^{\mathrm{mb}}_n) = c_n$.

**Binary closed form.** If $n = \sum_{j=1}^{\ell} 2^{m_j}$ with $m_1 > m_2 > \dots > m_\ell \ge 0$ is the binary expansion of $n$, then

$$c_n = \sum_{j=2}^{\ell} 2^{m_j}\bigl(m_1 - m_j - 2(j-2)\bigr).$$

**Takagi-curve form.** Let $s(x)$ be the distance from $x \in \mathbb R$ to the nearest integer and $k_n = \lceil \log_2 n \rceil$. Then

$$c_n = \sum_{j=1}^{k_n - 1} 2^j\, s(2^{-j} n) = 2^{k_n - 1}\, \mathcal T\!\left(\frac{n}{2^{k_n-1}} - 1\right),$$

where $\mathcal T(x) = \sum_{i \ge 0} 2^{-i} s(2^i x)$ on $[0,1]$ is the Takagi (blancmange) function.

**Properties.** For every $m \ge 0$, $c_{2^m + 1} = m$; for every $n \ge 1$, $c_n < 2^{\lceil \log_2 n \rceil}/3$ and $c_n < n/2$; and for $m \ge 1$ and $1 \le p \le 2^m - 1$, $c_{2^m + p} = c_{2^{m+1} - p}$. Moreover $c_n = n - 1 - \log_2 A(T^{\mathrm{mb}}_n)$, where $A$ counts automorphisms of the tree shape.

## Depends on

- [Colless index and its root decomposition](colless-index.md)

## Expansion

By the root decomposition, a minimal tree has minimal pending subtrees, which gives the first recurrence. Minimality of the even split $(\lceil n/2 \rceil, \lfloor n/2 \rfloor)$ is proved by induction, and $C(T) \ge C(T^{\mathrm{mb}}_n)$ for every $T$ then follows. The closed forms are verified against the recurrence by induction on $n$, separating even and odd $n$; the Takagi form explains the fractal, self-similar shape of the sequence and, with the known maximum $2/3$ of $\mathcal T$, yields the bound $c_n < 2^{k_n}/3$. In the maximally balanced tree every balance value is $0$ or $1$, and a node has balance $0$ exactly when its two pending subtrees are isomorphic, which gives the automorphism formula.

## Sources

- T. M. Coronado, M. Fischer, L. Herbst, F. Rosselló and K. Wicke, "On the minimum value of the Colless index and the bifurcating trees that achieve it", *Journal of Mathematical Biology* (2020), <https://doi.org/10.1007/s00285-020-01488-9> (Lemma 2, Theorem 1, Corollaries 2–5, Theorems 2 and 3; numbering as in the arXiv version 1907.05064v2).
