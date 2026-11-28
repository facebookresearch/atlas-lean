# Deque and traversal conjectures for splay trees

The *deque conjecture* (Tarjan 1985) asserts that, starting from any splay tree on $n$ keys, any sequence of $m$ deque operations (push and inject, which add a new minimum or maximum key, and pop and eject, which splay the minimum or maximum key to the root and delete it) costs $O(m + n)$. The *traversal conjecture* (Sleator and Tarjan 1985) asserts that for any two BSTs $T_1, T_2$ on the same $n$ keys, starting from $T_1$ and accessing the keys by splaying in the preorder of $T_2$ costs $O(n)$. Both are open. The traversal conjecture follows from the dynamic optimality conjecture (Sleator and Tarjan, Section 7), and the deque conjecture is a corollary of dynamic optimality as restated by Pettie (Section 1); in both cases the offline optimum is $O(m + n)$ on these sequences.

## Depends on

- [Dynamic optimality](../dynamic-optimality/dynamic-optimality.md)
- [Splay operation](../splay-tree/splay.md)

## Sources

- Daniel D. Sleator, Robert E. Tarjan, "Self-Adjusting Binary Search Trees", Journal of the ACM 32(3) (1985), Section 7 (Conjectures 1 and 3, and the implication from dynamic optimality to the traversal conjecture).
- Robert E. Tarjan, "Sequential Access in Splay Trees Takes Linear Time", Combinatorica 5(4) (1985).
- Seth Pettie, "Splay Trees, Davenport–Schinzel Sequences, and the Deque Conjecture", SODA (2008), arXiv:0707.2160, Section 1 (the deque conjecture among the corollaries of dynamic optimality).
