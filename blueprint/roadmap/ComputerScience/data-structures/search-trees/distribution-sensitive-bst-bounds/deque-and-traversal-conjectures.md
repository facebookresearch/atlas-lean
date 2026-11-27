# Deque and traversal conjectures for splay trees

The *deque conjecture* (Tarjan 1985) asserts that, starting from any splay tree on $n$ keys, any sequence of $m$ deque operations (push and inject, which add a new minimum or maximum key, and pop and eject, which splay the minimum or maximum key to the root and delete it) costs $O(m + n)$. The *traversal conjecture* (Sleator and Tarjan 1985) asserts that for any two BSTs $T_1, T_2$ on the same $n$ keys, starting from $T_1$ and accessing the keys by splaying in the preorder of $T_2$ costs $O(n)$. Both are open, and both would follow from the dynamic optimality of splay trees (for the deque conjecture, in Sleator and Tarjan's form that also allows insertions and deletions), since the offline optimum is $O(m + n)$ on these sequences.

## Depends on

- [Dynamic optimality](../dynamic-optimality/dynamic-optimality.md)
- [Splay operation](../splay-tree/splay.md)

## Sources

- Daniel D. Sleator, Robert E. Tarjan, "Self-Adjusting Binary Search Trees", Journal of the ACM 32(3) (1985).
- Robert E. Tarjan, "Sequential Access in Splay Trees Takes Linear Time", Combinatorica 5(4) (1985).
- Seth Pettie, "Splay Trees, Davenport–Schinzel Sequences, and the Deque Conjecture", SODA (2008), arXiv:0707.2160.
