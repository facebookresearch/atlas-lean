# Static finger theorem for splay trees

For every splay tree on a key set $s$ with $|s| = n$, every finger $f \in s$, and every sequence of $m$ accesses $x_1, \dots, x_m$ to keys of $s$, the total splaying cost (rotations, with at least one unit per access) satisfies

$$
\sum_{j=1}^m \mathrm{cost}(x_j) = O\left(n \log n + m + \sum_{j=1}^m \log\left(d(f, x_j) + 1\right)\right),
$$

with explicit constants independent of $n$, $m$ and $f$.

## Proof sketch

Apply the weighted access lemma with weights $w(y) = 1/(d(f,y) + 1)^2$. The total weight is at most $3$, since the distances on each side of the finger are distinct and $\sum_{k \ge 1} 1/k^2 \le 2$. The amortized cost of accessing $y$ is then $O(\log(W / w(y))) = O(\log(d(f,y) + 1) + 1)$, and the initial potential exceeds the final one by $O(n \log n)$.

## Depends on

- [Finger distance and working-set numbers of an access sequence](finger-distance-and-working-set-numbers.md)
- [Splay-tree potential](../splay-tree/potential.md)

## Proof depends on

- [Access lemma for splay trees](../splay-tree/access-lemma-weighted.md)

## Sources

- D. D. Sleator and R. E. Tarjan, "Self-Adjusting Binary Search Trees", Journal of the ACM 32(3), 1985.
