# Deque and traversal conjectures for splay trees

The *deque conjecture* (Tarjan 1985) asserts that any sequence of $m$ deque operations (insertions and deletions at the minimum or maximum key) on a splay tree initially holding $n$ keys costs $O(m + n)$. The *traversal conjecture* (Sleator and Tarjan 1985) asserts that for any two BSTs $T_1, T_2$ on the same $n$ keys, accessing the keys of $T_2$ in preorder by splaying, starting from $T_1$, costs $O(n)$. Both are special cases of dynamic optimality for splay trees, since the offline optimum is $O(m + n)$ on these sequences.

## Depends on

- [Dynamic optimality](../dynamic-optimality/dynamic-optimality.md)
- [Splay operation](../splay-tree/splay.md)

## Sources

- Daniel D. Sleator, Robert E. Tarjan, "Self-Adjusting Binary Search Trees", Journal of the ACM 32(3) (1985).
- Robert E. Tarjan, "Sequential Access in Splay Trees Takes Linear Time", Combinatorica 5(4) (1985).
