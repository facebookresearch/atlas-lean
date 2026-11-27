# Structures achieving the unified bound

There is a comparison-based dynamic dictionary on the pointer machine, the *unified structure*, which is a collection of search trees rather than a single BST, in which the amortized cost of accessing $x$ is $O\big(\min_y \log_2(w(y) + d(x, y) + 2)\big)$, where $y$ ranges over the stored keys, $w(y)$ is the number of distinct keys accessed since the last access to $y$ and $d(x, y)$ is the rank distance; it also supports insertions and deletions within this bound and has worst-case access time $O(\log n)$. Among binary search trees, the skip-splay tree serves every access sequence $X$ of length $m$ on $n$ keys in time $O(m \log\log n + \mathrm{UB}(X))$, with the unified bound normalized as by Derryberry and Sleator (the window count includes the key itself, and is $n$ for a key not accessed before).

## Proof sketch

The unified structure builds on Iacono's working-set structure, which keeps the keys in $O(\log\log n)$ search trees of doubly exponentially growing sizes ordered by recency of access, and adds finger-search machinery so that an access is charged to the tier and key distance of the minimizing earlier access. Skip-splay trees partition a BST into $O(\log\log n)$ levels of splay trees of doubly exponentially decreasing sizes; an access splays within one splay tree per level, and summing local working-set costs over the levels gives the unified bound plus $O(1)$ per level.

## Depends on

- [Iacono's unified bound](unified-bound.md)

## Sources

- Mihai Bădoiu, Richard Cole, Erik D. Demaine, John Iacono, "A Unified Access Bound on Comparison-Based Dynamic Dictionaries", Theoretical Computer Science 382(2) (2007).
- Jonathan C. Derryberry, Daniel D. Sleator, "Skip-Splay: Toward Achieving the Unified Bound in the BST Model", WADS (2009).
