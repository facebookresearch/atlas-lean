# Key-independent optimality

For an access sequence $X$ of length $m$ on $[n]$ and a uniformly random permutation $\pi$ of $[n]$, let $\pi(X)$ be $X$ with every key relabeled by $\pi$. Then $\mathbb{E}_\pi[\mathrm{OPT}(\pi(X))] = \Theta(\mathrm{WS}(X) + n \log n)$ (Chalermsook, Goswami, Kozma, Mehlhorn and Saranurak, Theorem 11, the quantitative form of Iacono's theorem, whose statement omits the additive $n \log n$); in particular $\mathbb{E}_\pi[\mathrm{OPT}(\pi(X))] = \Theta(\mathrm{WS}(X))$ whenever $m \ge n \log_2 n$. Consequently any BST satisfying the working-set bound, splay trees in particular, is *key-independently optimal*: its cost on $\pi(X)$, in expectation over $\pi$, is within a constant factor of $\mathbb{E}_\pi[\mathrm{OPT}(\pi(X))]$, up to the same additive term.

## Proof sketch

The upper bound holds since the working-set bound is invariant under relabeling and achieved by splay trees. For the lower bound, fix an access $x_t$ and keep only the last accesses, before time $t$, to the $\omega_t$ keys of its working set; a random relabeling places these keys in uniformly random key order. The funnel of $x_t$ then contains, in expectation, $\Theta(\log(\omega_t + 2))$ keys on each side, which interleave in time $\Omega(\log(\omega_t + 2))$ times, so Wilber's second (funnel) bound has expectation $\Omega(\log(\omega_t + 2))$ per access.

## Depends on

- [Dynamic finger bound](dynamic-finger-bound.md)
- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)
- [Splay operation](../splay-tree/splay.md)

## Proof depends on

- [Working-set theorem for splay trees](../splay-tree-locality-theorems/working-set-theorem.md)
- [Wilber's second lower bound](../wilber-and-funnel-lower-bounds/wilber-second-bound.md)

## Sources

- John Iacono, "Key-Independent Optimality", Algorithmica 42(1) (2005); ISAAC (2002).
- Parinya Chalermsook, Mayank Goswami, László Kozma, Kurt Mehlhorn, Thatchaphol Saranurak, "The Landscape of Bounds for Binary Search Trees", arXiv:1603.04892, Section 3.3, Theorem 11 and footnote 1 (the term $n \log n$ is missing in Iacono's statement).
