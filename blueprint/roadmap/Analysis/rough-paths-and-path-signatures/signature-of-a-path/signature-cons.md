# First-letter recursion of the signature

Let every component of the velocity of $X$ be continuous. For all reals $c, b$, every letter $i$
and every word $w$,

$$S(X)^{i\,w}_{c,b} = \int_c^b v^i(r)\, S(X)^{w}_{r,b}\, dr .$$

The definition integrates the last letter last; this identity integrates the first letter last,
so, for $c \le b$, both readings of $\int_{c < t_1 < \cdots < t_k < b} dX^{i_1}_{t_1} \cdots dX^{i_k}_{t_k}$
agree; the identity itself holds for all $c, b$, with oriented integrals. The proof avoids Fubini's theorem: both sides vanish at $c = b$ and have the same
derivative in $c$, by the [lower-endpoint derivative](has-deriv-at-signature-lower.md).
