# Littlestone's Winnow mistake bound $\alpha k(\log_\alpha\theta + 1) + n/\theta$

Let every example of a finite sequence over $\{0,1\}^n$ be labelled by a monotone disjunction of $k$ variables. If $\alpha > 1$ and $\alpha\theta \ge 1$, then WINNOW1, with any tie rule, makes at most

$$
\alpha k\left(\log_\alpha \theta + 1\right) + \frac{n}{\theta}
$$

mistakes, independent of the sequence length. Specializations: $\alpha = 2, \theta = n$ gives at most $2k(\log_2 n + 1) + 1$; for $1 \le k \le n$, $\alpha = 2, \theta = n/k$ gives at most $2k\log_2(n/k) + 3k$.

## Proof sketch

Let $u$ and $v$ count promotion and elimination steps. The total weight starts at $n$, grows by at most $(\alpha - 1)\theta$ per promotion and drops by at least $\theta$ per elimination, and stays nonnegative, so $v \le n/\theta + (\alpha-1)u$. Each relevant weight never exceeds $\alpha\theta$ and is never eliminated, while every promotion multiplies some relevant weight by $\alpha$; hence $u \le k(\log_\alpha\theta + 1)$. Add $u + v$.

## Depends on

- [Winnow (WINNOW1) for monotone disjunctions](winnow1-algorithm.md)

## Sources

- Nick Littlestone, "Learning Quickly When Irrelevant Attributes Abound: A New Linear-Threshold Algorithm", Machine Learning 2(4), 1988.
