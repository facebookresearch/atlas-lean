# Working-set theorem for splay trees

For every splay tree on a key set of size $n$ and every sequence of $m$ accesses $x_1, \dots, x_m$ to stored keys with working-set numbers $t(1), \dots, t(m)$, the total splaying cost satisfies

$$
\sum_{j=1}^m \mathrm{cost}(x_j) = O\left(n \log n + m + \sum_{j=1}^m \log\left(t(j) + 1\right)\right),
$$

with explicit constants. Thus recently accessed keys are cheap to access again.

## Proof sketch

Use time-varying weights: before access $j$, give the key with recency rank $r$ weight $1/(r+1)^2$, total at most $2$. The access lemma bounds the amortized cost of access $j$ by $O(\log(t(j) + 1) + 1)$. Resetting the accessed key to rank $1$ only increases its own weight and does not increase the potential of the other keys, so the potential changes telescope up to $O(n \log n)$.

## Depends on

- [Finger distance and working-set numbers of an access sequence](finger-distance-and-working-set-numbers.md)
- [Splay-tree potential](../splay-tree/potential.md)

## Proof depends on

- [Access lemma for splay trees](../splay-tree/access-lemma-weighted.md)

## Sources

- D. D. Sleator and R. E. Tarjan, "Self-Adjusting Binary Search Trees", Journal of the ACM 32(3), 1985.
