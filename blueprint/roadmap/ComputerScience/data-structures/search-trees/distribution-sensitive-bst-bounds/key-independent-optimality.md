# Key-independent optimality

For every access sequence $X$ on $[n]$ and a uniformly random permutation $\pi$ of $[n]$, let $\pi(X)$ be $X$ with every key relabeled by $\pi$. Then $\mathbb{E}_\pi[\mathrm{OPT}(\pi(X))] = \Theta(\mathrm{WS}(X) + m)$. Consequently any BST satisfying the working-set bound, splay trees in particular, is *key-independently optimal*: its cost on $\pi(X)$ is within a constant factor of $\mathbb{E}_\pi[\mathrm{OPT}(\pi(X))]$.

## Proof sketch

The upper bound holds since the working-set bound is invariant under relabeling and achieved by splay trees. For the lower bound, under a random relabeling the keys accessed at distinct times are in random relative order, so Wilber's first bound with a fixed balanced reference tree, applied to the relabeled sequence, has expectation $\Omega(\log(\omega_t + 2))$ per access by an analysis of how many reference-tree alternations a random embedding of the recent working set induces.

## Depends on

- [Dynamic finger bound](dynamic-finger-bound.md)
- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)
- [Splay operation](../splay-tree/splay.md)

## Proof depends on

- [Wilber's first lower bound](../wilber-and-funnel-lower-bounds/wilber-first-bound.md)

## Sources

- John Iacono, "Key-Independent Optimality", Algorithmica 42(1) (2005).
