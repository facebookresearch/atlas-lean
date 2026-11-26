# Roots of a weighted bivariate polynomial lie near prescribed branches

Let $n, w \in \mathbb{N}$ and let $F = \sum_k F_k(t)\, y^k$ be a polynomial in $y$ with coefficients $F_k \in \mathbb{C}[t]$, with $\deg_y F \le n$. Assume:

- (weight bound) for all $k, j$ with $w\,(n \mathbin{\dot-} k) < j$, the coefficient of $t^j$ in $F_k$ is $0$, where $\dot-$ is truncated subtraction;
- the leading coefficient $F_n$ is a nonzero constant $c \in \mathbb{C}$;
- $P_0, \dots, P_{n-1} \in \mathbb{C}[t]$ have degree at most $w$, and their coefficients of $t^w$ are pairwise distinct;
- the remainder $G = F - c \prod_{i} (y - P_i(t))$ satisfies: for all $k, j$ with $w\,(n \mathbin{\dot-} k) \le j + w$, the coefficient of $t^j y^k$ in $G$ is $0$.

Then there are real numbers $C_0 > 0$ and $T$ such that for every $t \in \mathbb{C}$ with $|t| \ge T$ and every root $x \in \mathbb{C}$ of $y \mapsto F(t, y)$ there is an index $i$ with

$$
|x - P_i(t)| \le \frac{C_0}{|t|}.
$$
