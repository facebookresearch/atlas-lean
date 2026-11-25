# Containment of a point pattern in a set of grid cells

A set of cells
$A \subseteq \mathbb{N} \times \mathbb{N}$, each cell written (column, row), contains a set
$P \subseteq \mathbb{R}^2$ when there are maps $f_X, f_Y : \mathbb{R} \to \mathbb{N}$ such that
$f_X$ is strictly increasing on the set of $x$-coordinates of points of $P$, $f_Y$ is strictly
increasing on the set of $y$-coordinates of points of $P$, and $(f_X(x), f_Y(y)) \in A$ for every
$(x, y) \in P$.

For finite $P$ this is containment of the 0-1 matrix $M_P$ of $P$ (rows of $P$ listed bottom to
top; flipping the rows of both matrices preserves containment).

## Sources

- Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 1 (0-1 matrix containment and the matrix `M_P` of a finite point set).
