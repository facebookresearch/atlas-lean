# Knuth's quadratic algorithm for optimal binary search trees

Fill the table of the interval recurrence by increasing interval length, but for $(i, j)$ scan only the roots $k \in [K(i, j-1), K(i+1, j)]$. This window algorithm returns the optimal cost $c(0, n)$ and an optimal tree whenever $w$ satisfies the quadrangle inequality and is monotone on intervals, in particular for optimal binary search trees. The total window length summed over all intervals of a fixed length telescopes to $O(n)$, so the algorithm makes $O(n^2)$ root evaluations, and on the word RAM it runs in $O(n^2)$ instructions (against $O(n^3)$ for the plain scan).

## Proof sketch

Correctness is root monotonicity; for each length $d \ge 2$, $\sum_{i=0}^{n-d} (K(i+1, i+d) - K(i, i+d-1) + 1)$ telescopes to $K(n-d+1, n) - K(0, d-1) + n - d + 1 \le 2n$.

## Depends on

- [The quadrangle inequality and monotonicity on intervals](quadrangle-inequality.md)
- [Optimal binary search tree procedure](../optimal-binary-search-tree/optimal-bst.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Monotonicity of optimal roots](monotone-optimal-roots.md)
- [Yao's theorem: the quadrangle inequality propagates to the optimal cost](yao-quadrangle-inequality-theorem.md)
- [The optimal BST procedure finds the minimum expected search cost](../optimal-binary-search-tree/optimal-bst-minimal.md)

## Sources

- D. E. Knuth, "Optimum Binary Search Trees", Acta Informatica 1, 1971.
- F. F. Yao, "Efficient Dynamic Programming Using Quadrangle Inequalities", Proceedings of the 12th ACM Symposium on Theory of Computing (STOC), 1980.
