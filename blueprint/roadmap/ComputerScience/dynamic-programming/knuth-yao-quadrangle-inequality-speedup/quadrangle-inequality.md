# The quadrangle inequality and monotonicity on intervals

A function $f$ on intervals $0 \le i \le j \le n$ satisfies the **quadrangle inequality** if $f(i, j) + f(i', j') \le f(i, j') + f(i', j)$ whenever $i \le i' \le j \le j'$, and is **monotone on intervals** if $f(i', j) \le f(i, j')$ whenever $[i', j] \subseteq [i, j']$. Consider the **interval recurrence** $c(i, i) = 0$ and $c(i, j) = w(i, j) + \min_{i < k \le j} \big(c(i, k-1) + c(k, j)\big)$ for $i < j$, and let $K(i, j)$ be the largest minimizing root $k$. With Knuth's weight $w(i, j) = \sum_{i < k \le j} p_k + \sum_{i \le g \le j} q_g$, $c(0, n)$ is the minimum weighted search cost of a binary search tree on keys $1, \dots, n$.

## Depends on

- [Optimal BST table recurrence](../optimal-binary-search-tree/optimal-bst-table-spec.md)

## Sources

- F. F. Yao, "Efficient Dynamic Programming Using Quadrangle Inequalities", Proceedings of the 12th ACM Symposium on Theory of Computing (STOC), 1980.
- D. E. Knuth, "Optimum Binary Search Trees", Acta Informatica 1, 1971.
