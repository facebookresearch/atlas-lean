# Monotonicity of optimal roots

If the optimal cost $c$ satisfies the quadrangle inequality, then the largest optimal roots satisfy

$$
K(i, j - 1) \le K(i, j) \le K(i + 1, j) \qquad (i + 1 < j).
$$

## Proof sketch

If a root $k < K(i, j-1)$ were better for $(i, j)$, the quadrangle inequality applied to $c(k, j-1), c(k', j)$ would make it better for $(i, j-1)$ too.

## Depends on

- [The quadrangle inequality and monotonicity on intervals](quadrangle-inequality.md)

## Proof depends on

- [Yao's theorem: the quadrangle inequality propagates to the optimal cost](yao-quadrangle-inequality-theorem.md)

## Sources

- F. F. Yao, "Efficient Dynamic Programming Using Quadrangle Inequalities", Proceedings of the 12th ACM Symposium on Theory of Computing (STOC), 1980.
- D. E. Knuth, "Optimum Binary Search Trees", Acta Informatica 1, 1971.
