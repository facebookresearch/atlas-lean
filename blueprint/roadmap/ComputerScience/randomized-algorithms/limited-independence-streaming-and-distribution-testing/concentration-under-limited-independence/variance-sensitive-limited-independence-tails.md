# Variance-sensitive tail bounds for [0,1] sums under limited independence

Let $h$ be $2m$-wise independent with uniform seed, $R \subseteq X$ finite, and $g_z : Y \to [0,1]$ with total mean $\sum_{z \in R}\mathbb{E}_y g_z(y) \le \mu$ and $2m \le 3\mu$. Then

$$
\mathbb{E}_i\Bigl(\sum_{z\in R}\bigl(g_z(h_i(z)) - \mathbb{E}_y g_z(y)\bigr)\Bigr)^{2m} \le 2(3m\mu)^m, \qquad \Pr_i\bigl[|\textstyle\sum_z (\cdots)| \ge a\bigr] \le 2\Bigl(\frac{3m\mu}{a^2}\Bigr)^m ,
$$

so the tail is at most $2 \cdot 2^{-m}$ when $6m\mu \le a^2$ and $a \le \mu$. The bound scales with the mean $\mu$ rather than with $|R|$, as needed for balls-into-bins indicators; the same holds for $[0,1]$-valued functions of disjoint restrictions of $h$ of size at most $K$ under $2mK$-wise independence.

## Proof sketch

Group $2m$-tuples by the number $r \le m$ of distinct points; tuples with a singleton fiber vanish, and for a point repeated $c \ge 2$ times $|\mathbb{E}(g - \mathbb{E}g)^c| \le \mathbb{E}g$. Counting tuples with image size $r$ using $r^r \le 3^r r!$ and summing a geometric series under $2m \le 3\mu$ gives the moment bound.

## Depends on

- [Moment and tail bounds under 2m-wise independence](moment-bounds-under-limited-independence.md)

## Sources

- J. P. Schmidt, A. Siegel and A. Srinivasan, "Chernoff–Hoeffding Bounds for Applications with Limited Independence", SIAM Journal on Discrete Mathematics, 1995.
- M. Bellare and J. Rompel, "Randomness-Efficient Oblivious Sampling", Proceedings of the 35th IEEE Symposium on Foundations of Computer Science, 1994.
