# Entries of the matrix $U_\alpha$

For a sequence $\alpha = (\alpha_0, \alpha_1, \dots)$
of rational numbers, the entries $U_{i,j}$ ($i, j \ge 1$) of the matrix $U_\alpha$ are defined by
recursion on the row index $i$. The first row is $U_{1,j} = \alpha_{j-1}$. For $i \ge 2$ the
first column is $U_{i,1} = 0$, and for $j \ge 2$

$$U_{i,j} = U_{i-1,j-1} + (j - i + 1)\, U_{i-1,j}.$$

Entries with $i = 0$ or $j = 0$ are set to $0$.
