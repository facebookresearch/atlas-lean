# Moment and tail bounds under 2m-wise independence

Let $m \ge 1$ and let $h : \iota \times X \to Y$ be $2m$-wise independent with uniform seed (so each $h_i(x)$ is uniform on the finite set $Y$), let $S \subseteq X$ be finite and nonempty, and let $Z_x : Y \to [0, 1]$ for $x \in S$. Then the random variables $Z_x(h_i(x))$, $x \in S$, are $2m$-wise independent with values in $[0, 1]$, and their average $A_i = \frac{1}{|S|}\sum_{x \in S} Z_x(h_i(x))$, with mean $\mu = \mathbb{E}_i A_i$, satisfies for every $\varepsilon > 0$

$$
\Pr_i\bigl[|A_i - \mu| \ge \varepsilon\bigr] \le \Bigl(\frac{(2m)^2}{4|S|\varepsilon^2}\Bigr)^{m} = \Bigl(\frac{m^2}{|S|\varepsilon^2}\Bigr)^{m}.
$$

## Proof sketch

Expand $\mathbb{E}\bigl(\sum_{x}(Z_x - \mathbb{E}Z_x)\bigr)^{2m}$: a tuple of points contributes zero unless every point appears at least twice, because the values at at most $2m$ points are independent and the centred terms have mean zero; so at most $m$ distinct points occur. Tuples with exactly $r$ distinct points number at most $|S|^r r^{2m}/r!$, and $\sum_{r \le m} r^{2m}/r! \le m^{2m}$, so the $2m$-th central moment of the sum is at most $m^{2m}|S|^m$, each term being at most $1$ in absolute value; Markov's inequality gives the tail. (Derived, not stated by the sources: the same count gives, for centred $Z_x : Y \to [-1, 1]$, the moment bound $\mathbb{E}_i\bigl(\sum_{x} Z_x(h_i(x))\bigr)^{2m} \le m^{2m}|S|^m$ and the tail $(m^2|S|/a^2)^m$ for the sum at threshold $a > 0$; if moreover $\mathbb{E}_y Z_x(y)^2 \le v_x$, a tuple contributes at most $\prod v_x$ over its distinct points, since $|Z_x|^c \le Z_x^2$ for $c \ge 2$, which replaces $|S|$ by $\max(\sum_{x} v_x, 1)$ at the cost of a factor $m$; hence $O(c\log n)$-wise independence gives concentration with failure probability $n^{-c}$.)

## Depends on

- [k-wise independent hash family](../../../data-structures/hashing/succinct-dictionaries-and-hash-families/word-ram-hash-families/k-wise-independent-hash-family.md)

## Sources

- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1–3), 2012: Proposition 3.28 (the pairwise case, for random variables with values in $[0, 1]$), the remark after Corollary 3.34, and Problem 3.8 ($k$-wise Independent Tail Inequality).
- M. Bellare and J. Rompel, "Randomness-Efficient Oblivious Sampling", Proceedings of the 35th IEEE Symposium on Foundations of Computer Science, 1994.
