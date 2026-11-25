# The root can be pushed to the end of its edge

Let $(P_t)$ be a [reversible semigroup](is-reversible-semigroup.md) for $\pi$. Then for all real leaf weights, trees $l, r$ and real $s, t$, the [site likelihood](../felsenstein-s-pruning-algorithm/likelihood.md) of the root with children $l, r$ on edges with weights $P_s, P_t$ is

$$\sum_b \pi(b)\, \mathrm{pr}(l, b) \sum_c P_{s+t}(b, c)\, \mathrm{pr}(r, c),$$

where $\mathrm{pr}$ is the [pruning recursion](../felsenstein-s-pruning-algorithm/prune.md): the likelihood of the root placed at the root of $l$, with $r$ at distance $s + t$.
