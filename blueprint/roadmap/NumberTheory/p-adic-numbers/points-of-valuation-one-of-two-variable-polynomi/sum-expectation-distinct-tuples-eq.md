# Sum of expectations over distinct tuples of points

Let $p$ be a prime, let
$f \in \mathbb{Z}[x, y]$ have partial derivatives $f_x$ and $f_y$, and let $C_f(\mathbb{F}_p)$
be the set of pairs of integers $0 \le r, s < p$ with $p \mid f(r, s)$. Suppose that no
$(r, s) \in C_f(\mathbb{F}_p)$ has $p \mid f_x(r, s)$ and $p \mid f_y(r, s)$, and let $k \ge 1$.
For a $k$-tuple $P$ of points of $C_f(\mathbb{F}_p)$, let $N(P)$ be the number of pairs
$(a, b)$ with $0 \le a, b < p$ such that $p^2 \mid f(r + ap, s + bp)$ for every point $(r, s)$
of $P$. Then

$$
\sum_P \frac{N(P)}{p^2} = \frac{m_k(f, p)}{p^2} + \frac{o_k(f, p)}{p},
$$

where $P$ runs over the $k$-tuples of pairwise distinct points of $C_f(\mathbb{F}_p)$. Here
$m_k(f, p)$ is the number of such $P$ whose matrix $B_k(P)$, with rows
$(f_x(r, s), f_y(r, s), f(r, s)/p)$ modulo $p$ at the points of $P$, has rank $2$ and whose first
two columns have rank $2$, and $o_k(f, p)$ is the number of such $P$ for which $B_k(P)$ has rank
$1$ and its first two columns are not both zero.

In the paper's notation the left side is $\sum_{l_1 \ne \dots \ne l_k} E[Y_{l_1} \cdots Y_{l_k}]$
(eq. (15)). The hypothesis is the paper's standing assumption of Section 3 at this $p$; its
proof uses it to rule out rank $0$.

## Sources

- Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Proposition 6, eq. (15) (`integers-2026-A82-prop-6`).
