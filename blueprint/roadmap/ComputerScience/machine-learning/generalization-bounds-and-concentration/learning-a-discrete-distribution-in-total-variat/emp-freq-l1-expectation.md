# Expected L¹ error of the empirical frequencies

Let $p$ be a probability mass function on a finite set $\alpha$ with $k$ elements, and let $n \ge 1$. For a sample $x \in \alpha^n$ drawn i.i.d. from $p$, the expected $L^1$ distance between the empirical frequencies $\hat p_x$ and $p$ is at most $\sqrt{k/n}$:

$$\sum_{x \in \alpha^n} \Bigl(\prod_{i} p(x_i)\Bigr) \sum_{a \in \alpha} |\hat p_x(a) - p(a)| \le \sqrt{k/n}.$$

This is a bound on the $L^1$ distance $\sum_a |\hat p_x(a) - p(a)|$. Under the usual convention that the total variation distance is half the $L^1$ distance, it gives the expected total variation bound $\tfrac12 \sqrt{k/n}$, which is a consequence and not the statement itself.
