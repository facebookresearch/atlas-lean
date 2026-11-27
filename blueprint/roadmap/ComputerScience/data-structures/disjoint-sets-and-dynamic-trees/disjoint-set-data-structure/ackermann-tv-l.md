# Tarjan–van Leeuwen's Ackermann function

For $i, j \ge 1$:

$$A(1, j) = 2^j, \qquad A(i, 1) = A(i - 1, 2) \ (i \ge 2), \qquad A(i, j) = A(i - 1, A(i, j - 1)) \ (i, j \ge 2).$$

At the boundary, $A(0, j) = 0$ for every $j$, $A(1, 0) = 2^0 = 1$, and $A(i, 0) = 0$ for
$i \ge 2$. For example $A(2, 1) = 4$, $A(2, 2) = A(3, 1) = 16$. This variant starts from
$A(1, j) = 2^j$ instead of the $j + 1$ of the Ackermann–Péter function; by Tarjan and van
Leeuwen's Remark 1, the change only adds a constant to the inverse function.

## Sources

- R. E. Tarjan and J. van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2)
  (1984) 245–281, §1, definition of $A$ and Remarks 1–2.
