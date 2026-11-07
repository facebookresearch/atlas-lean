# Shearer's entropy inequality

Let $\alpha$ be a nonempty finite set, $n$ a natural number,
and $\mu$ a probability mass function on $\alpha^n$, that is, $\mu(x) \ge 0$ for all
$x \in \alpha^n$ and $\sum_{x \in \alpha^n} \mu(x) = 1$. Write $H(\mu)$ for the full entropy of
$\mu$ and, for a set $S$ of coordinates in $\{0, \dots, n-1\}$, write $H_S(\mu)$ for the
marginal entropy of $\mu$ on $S$. Let $C$ be a set of subsets of $\{0, \dots, n-1\}$ and
$k \ge 1$ an integer such that every coordinate lies in at least $k$ members of $C$. Then
$k \, H(\mu) \le \sum_{S \in C} H_S(\mu)$.

## Sources

- F. R. K. Chung et al., J. Combin. Theory A 43 (1986), DOI 10.1016/0097-3165(86)90019-1. It follows from `shearer_entropy_inequality_general`; the hypothesis `hk` is unused and keeps the source's shape. Proves `Wanted` entry `shearer_entropy_inequality`.
