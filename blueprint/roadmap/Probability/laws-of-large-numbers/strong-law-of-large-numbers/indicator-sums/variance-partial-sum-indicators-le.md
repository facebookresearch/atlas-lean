# Variance of a sum of pairwise independent indicators is at most its mean

Let $\mu$ be
a probability measure on $\Omega$ and let $A_0, A_1, \dots$ be pairwise independent measurable
subsets of $\Omega$. Then for every $n$, the partial sum $S_n = \sum_{i < n} 1_{A_i}$ satisfies
$\operatorname{Var}(S_n) \le \mathbb{E}[S_n]$, where variance and expectation are taken
with respect to $\mu$.

This follows from $\operatorname{Var}(1_{A_i}) \le \mu(A_i)$ and the fact that pairwise
independence makes covariances vanish.
