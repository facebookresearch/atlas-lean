# Structures achieving the unified bound

There is a comparison-based dynamic dictionary (a pointer structure that is not a BST) that serves every access sequence $X$ of length $m$ on $n$ keys in total time $O(m + n + \mathrm{UB}(X))$. Among binary search trees, the skip-splay tree serves $X$ with cost $O(m \log\log n + n + \mathrm{UB}(X))$.

## Proof sketch

Bădoiu, Cole, Demaine and Iacono maintain the keys in a sequence of working-set-style tiers of doubly exponentially growing size, each storing fingers searchable in time logarithmic in key distance, and charge an access to the tier containing the minimizing earlier access. Skip-splay trees partition a BST into $O(\log\log n)$ levels of splay trees of doubly exponentially decreasing size and splay within each level, which costs the unified bound plus $O(1)$ per level.

## Depends on

- [Iacono's unified bound](unified-bound.md)

## Sources

- Mihai Bădoiu, Richard Cole, Erik D. Demaine, John Iacono, "A Unified Access Bound on Comparison-Based Dynamic Dictionaries", Theoretical Computer Science 382(2) (2007).
- Jonathan C. Derryberry, Daniel D. Sleator, "Skip-Splay: Toward Achieving the Unified Bound in the BST Model", WADS (2009).
