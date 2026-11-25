# Rank bound and amortized costs of Fibonacci heaps

A [Fibonacci heap](fibonacci-heap.md) is a collection of heap-ordered trees. Some non-root nodes are *marked*. Its operations work as follows:
- $\mathrm{insert}$ and $\mathrm{meld}$ add trees to the root list;
- $\mathrm{extract\text{-}min}$ removes the minimum root, adds its children to the root list, and *consolidates* by repeatedly linking two roots of equal rank (number of children), the larger key becoming a child of the smaller, until all root ranks are distinct;
- $\mathrm{decrease\text{-}key}$ cuts the node from its parent and makes it a root. If the parent was already marked, the cut *cascades* to the parent, and so on up the tree. The first unmarked ancestor reached, if it is not a root, becomes marked.

**Theorem.**
1. **Rank bound.** In a Fibonacci heap with $n$ elements, every node has rank at most $\log_\varphi n$, where $\varphi = (1 + \sqrt 5)/2$. A node of rank $k$ has at least $F_{k+2} \ge \varphi^k$ descendants, counting itself.
2. **Amortized costs.** With potential $\Phi(H) = \mathrm{trees}(H) + 2 \cdot \mathrm{marks}(H)$:
    - $\mathrm{insert}$, $\mathrm{meld}$, $\mathrm{find\text{-}min}$ and $\mathrm{decrease\text{-}key}$ take $O(1)$ amortized time;
    - $\mathrm{extract\text{-}min}$ takes $O(\log n)$ amortized time.

    Hence any sequence of $m$ operations, $n$ of them insertions, starting from an empty heap takes $O(m + n\log n)$ time.

**Proof.**
1. Let $y_1, \dots, y_k$ be the children of a node $x$ in the order they were linked to $x$. When $y_i$ was linked, $x$ had at least $i - 1$ children, and linked roots have equal rank. Since then $y_i$ has lost at most one child, or it would have been cut. So $\mathrm{rank}(y_i) \ge i - 2$ for $i \ge 2$. If $s_k$ is the minimum size of a subtree of rank $k$, this gives $s_k \ge 2 + \sum_{i=0}^{k-2} s_i$. Induction with $F_{k+2} = 1 + \sum_{i \le k} F_i$ gives $s_k \ge F_{k+2}$, and $F_{k+2} \ge \varphi^k$.
2. Consolidation costs $O(\mathrm{rank} + \mathrm{trees})$ and leaves at most $\mathrm{rank} + 1$ trees, so the potential pays for the trees beyond that. A decrease-key with $c$ cascading cuts does $O(c)$ work. It adds at most $c$ trees and removes at least $c - 2$ marks, so $\Delta\Phi \le c + 2(2 - c) = 4 - c$, and the amortized cost is $O(1)$.

## Depends on

- [Fibonacci heap](fibonacci-heap.md)

## Background

- [The degree of a valid Fibonacci tree is less than its size](degree-lt-card.md)
- [Consolidation yields distinct root degrees](consolidate-degrees-nodup.md)

## Sources

- K. Wayne, *Fibonacci Heaps*, lecture slides for J. Kleinberg and É. Tardos, *Algorithm Design*, Princeton University, <https://www.cs.princeton.edu/~wayne/kleinberg-tardos/pdf/FibonacciHeaps.pdf>: the Fredman–Tarjan theorem ($m$ operations including $n$ insertions take $O(m + n\log n)$ time), the potential $\Phi(H) = \mathrm{trees}(H) + 2 \cdot \mathrm{marks}(H)$, the amortized analyses of insert, extract-min and decrease-key with cascading cuts, Lemma 1 ($\mathrm{rank}(y_i) \ge i - 2$), Lemma 2 ($s_k \ge F_{k+2}$), the Fibonacci lemma ($\mathrm{rank}(H) \le \log_\varphi n$), and the Fibonacci facts.
