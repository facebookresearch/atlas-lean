# Apply computes the operation pointwise

For every binary Boolean operation
$\mathrm{op}$, all binary decision diagrams $t_1$ and $t_2$, and every assignment $\sigma$ of
Boolean values to the variables, the value under $\sigma$ of the diagram
$\mathrm{apply}(\mathrm{op}, t_1, t_2)$ obtained from $t_1$ and $t_2$ by Bryant's apply operation
under $\mathrm{op}$ is $\mathrm{op}(a_1, a_2)$, where $a_i$ is the value of $t_i$ under $\sigma$.
