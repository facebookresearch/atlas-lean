# Model count by enumeration

An assignment is a map $\sigma$ from the variables, which are
natural numbers, to the truth values $\mathrm{false}$ and $\mathrm{true}$. For a list
$x_1, \dots, x_k$ of variables, a function $f$ from assignments to truth values, and an assignment
$\sigma$, the model count of $f$ over $x_1, \dots, x_k$ from $\sigma$ is the number of tuples
$(b_1, \dots, b_k) \in \{\mathrm{false}, \mathrm{true}\}^k$ such that $f$ is true at the assignment
obtained from $\sigma$ by setting $x_1$ to $b_1$, then $x_2$ to $b_2$, and so on up to setting
$x_k$ to $b_k$, a later setting overriding an earlier one of the same variable.

When $x_1, \dots, x_k$ are distinct, this is the number of assignments that agree with $\sigma$
outside $x_1, \dots, x_k$ and make $f$ true.
