# Contribution of a split to the neighbor-joining score

For a finite set $X$, a subset $A \subseteq X$ and taxa $x, y$, put

$$g_A(x, y) = \begin{cases} |X \setminus A| & x, y \in A,\\ |A| & x, y \notin A,\\ 1 & \text{otherwise:}\end{cases}$$

the number of taxa on the far side of the split $\{A, X \setminus A\}$ when $x, y$ lie on the same side, and $1$ when the split separates them.
