# Moment and tail bounds under 2m-wise independence

Let $m \ge 1$ and let $h : \iota \times X \to Y$ be $2m$-wise independent with uniform seed (so each $h_i(x)$ is uniform on the finite set $Y$), $S \subseteq X$ finite, and $Z_x : Y \to [-1, 1]$ functions with $\mathbb{E}_{y}Z_x(y) = 0$, and let $a > 0$. Then

$$
\mathbb{E}_i\Bigl(\sum_{x \in S} Z_x(h_i(x))\Bigr)^{2m} \le m^{2m}|S|^m, \qquad \Pr_i\Bigl[\Bigl|\sum_{x\in S} Z_x(h_i(x))\Bigr| \ge a\Bigr] \le \Bigl(\frac{m^2|S|}{a^2}\Bigr)^m .
$$

If moreover $\mathbb{E}_y Z_x(y)^2 \le v_x$, the moment bound holds with $|S|$ replaced by $\max(\sum_{x\in S}v_x, 1)$ at the cost of a factor $m$, giving tail $m\,(m^2\max(\sum_x v_x, 1)/a^2)^m$; hence $O(c\log n)$-wise independence gives concentration with failure probability $n^{-c}$.

## Proof sketch

Expand the $2m$-th power. A tuple of points contributes zero unless every point appears at least twice, because the values at at most $2m$ points are independent and centered; so at most $m$ distinct points occur. Tuples with exactly $r$ distinct points number at most $|S|^r r^{2m}/r!$, and $\sum_{r \le m} r^{2m}/r! \le m^{2m}$, so there are at most $m^{2m}|S|^m$ such tuples, each contributing at most $1$; with variances, a tuple contributes at most $\prod v_x$ over its distinct points, since $|Z_x|^c \le Z_x^2$ for $c \ge 2$. Markov's inequality gives the tail.

## Depends on

- [k-wise independent hash family](../../../data-structures/hashing/succinct-dictionaries-and-hash-families/word-ram-hash-families/k-wise-independent-hash-family.md)

## Sources

- M. Bellare and J. Rompel, "Randomness-Efficient Oblivious Sampling", Proceedings of the 35th IEEE Symposium on Foundations of Computer Science, 1994.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science, 2012.
