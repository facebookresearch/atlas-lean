# Least-squares fitted values are the orthogonal projection onto the column space

For a real $n \times p$ matrix $X$ and $y \in \mathbb{R}^n$, let $P$ be the orthogonal projection onto the column space of $X$. The set of least-squares solutions $\{\beta : \|y - X\beta\| \text{ is minimal}\}$ is nonempty, and every least-squares solution has the same fitted vector $X\beta = Py$. The coefficient vector itself is unique if and only if $X$ has full column rank; otherwise the solutions form the affine set $\beta_0 + \ker X$. The full-rank case is the classical hat-matrix statement; the rank-deficient case follows from the same projection argument. The column space is finite-dimensional, hence closed and complete, and [admits an orthogonal projection](../../../Analysis/hilbert-spaces/of-complete-space.md). This makes $Py$ its unique nearest point to $y$. Two coefficient vectors have the same fit exactly when their difference lies in $\ker X$; rank–nullity identifies when that kernel is trivial.

## Sources

- G. Rodríguez, *Generalized Linear Models*, chapter 2 "Linear models for continuous data", Princeton University, <https://grodri.github.io/glms/notes/c2.pdf>, §2.2.1 (least-squares estimation, full-rank case) and §2.9.1 (the hat matrix)
