# Bounded total propensity on sublevel sets bounds the holding rates

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) on a set $S$ of species with
a finite set of reactions, [total propensity](total-rate.md) $\lambda$ and
[holding rate](hold-rate.md) $q$, and let $V : \mathbb{N}^S \to [0, \infty)$. Suppose that for every
real $m$ there is a $K$ with $\lambda(x) \le K$ for all states $x$ with $V(x) < m$. Then for every
$m \ge 0$ there is a $K'$ with $q(x) \le K'$ for all states $x$ with $V(x) < m$; one can take
$K' = \max(K, 1)$.
