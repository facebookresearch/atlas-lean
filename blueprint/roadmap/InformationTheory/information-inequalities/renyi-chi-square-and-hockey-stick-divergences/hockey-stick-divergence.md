# Hockey-stick divergence

Let $p, q$ be discrete probability distributions on a countable set $X$ and $c \in [0, \infty)$. The *hockey-stick divergence* at factor $c$ is

$$
E_c(p \,\|\, q) = \sum_{x \in X} \big(p(x) - c\, q(x)\big)_+ \in [0, 1],
$$

where $(t)_+ = \max(t, 0)$. It is antitone in $c$, vanishes iff $p(x) \le c\,q(x)$ for every $x$, and $E_1(p\|q)$ is the total variation distance $\sup_S |p(S) - q(S)|$.

## Depends on

- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- C. Dwork and A. Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science 9, 2014.
- P. Kairouz, S. Oh and P. Viswanath, "The Composition Theorem for Differential Privacy", IEEE Transactions on Information Theory 63(6), 2017.
