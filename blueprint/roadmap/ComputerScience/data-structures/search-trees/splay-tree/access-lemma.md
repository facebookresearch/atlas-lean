# Access lemma for splay trees (unit weights)

For every key $x$ and every binary tree $t$ (no search-tree ordering is assumed; $\log_2 0$ is
taken to be $0$, which matters only for the empty tree),

$$\mathrm{cost}(x, t) + \Phi(S_x(t)) - \Phi(t) \le 3\bigl(\log_2 |t| - \log_2 |f|\bigr) + 1,$$

where $S_x$ is the [splay operation](splay.md), $\Phi$ the [potential](potential.md), the cost is
the [number of rotations, or one if none](cost.md), $|\cdot|$ counts nodes and
$f = \mathrm{focus}(x, t)$ is the [subtree at the end of the search path](focus.md). It is the
[access lemma](access-lemma-weighted.md) with every weight equal to one.

## Informally uses

- [Access lemma for splay trees](access-lemma-weighted.md): the case $w = 1$.

## Sources

- D. D. Sleator and R. E. Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985)
  652–686, §2, Lemma 1 (Access Lemma), with every weight equal to one.
