# Volume of a grid drawing

A map $p$ from a set of vertices to $\mathbb{Z}^3$ has volume at most $N$ when some axis-aligned box $\prod_{i=1}^{3} [a_i, b_i]$ with integer $a_i, b_i$ contains every point $p(v)$ with $\prod_i (b_i - a_i + 1) \le N$. When the set of vertices is nonempty the box forces $a_i \le b_i$, and the product is its number of integer points. When it is empty the bounds may be reversed and the product can be zero or negative (for instance $a_1 = 1$, $b_1 = -1$, $a_2 = b_2 = a_3 = b_3 = 0$ gives $-1$), so the empty map has volume at most $N$ for every $N$.
