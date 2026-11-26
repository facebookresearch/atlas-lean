# The matrix $U_\alpha(n)$

For a sequence $\alpha = (\alpha_0, \alpha_1, \dots)$ of
rationals and a natural number $n$, $U_\alpha(n)$ is the $n \times n$ rational matrix whose
$(i, j)$ entry, for $1 \le i, j \le n$, is $U_{i,j}$, where $U_{1,j} = \alpha_{j-1}$ for
$j \ge 1$, $U_{i,1} = 0$ for $i \ge 2$, and $U_{i,j} = U_{i-1,j-1} + (j - i + 1) \, U_{i-1,j}$
for $i, j \ge 2$.
