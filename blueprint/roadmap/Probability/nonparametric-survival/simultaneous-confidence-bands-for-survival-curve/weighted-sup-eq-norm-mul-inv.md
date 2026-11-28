# Weighted sup statistic as a sup norm of a pointwise product

Let $\iota$ be a finite set and $w, v \in \mathbb{R}^\iota$. The [weighted sup statistic](weighted-sup.md) of $v$ with weights $w$ is the sup norm $\|(v_i / w_i)_i\|_\infty = \max_i |v_i / w_i|$, with real division ($x/0 = 0$) and with the sup norm of the empty vector equal to $0$. It equals the sup norm of the pointwise product of $v$ with the pointwise inverse of $w$:

$$
\max_i \left|\frac{v_i}{w_i}\right| = \big\|\big(v_i\, w_i^{-1}\big)_i\big\|_\infty,
$$

where $w_i^{-1} = 0$ when $w_i = 0$.
