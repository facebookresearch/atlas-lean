# Evaluating a flat environment

Let $\rho$ be a source environment, $\rho_t$ a target
environment, $\mathrm{acc}$ a map from natural numbers to target terms, and $i_1, \dots, i_n$ a
list of natural numbers. Write $\rho_i$ for the entry of $\rho$ at index $i$, counting from $0$.
Suppose every $i$ in the list is less than the length of $\rho$ and $\mathrm{acc}(i)$ evaluates
in $\rho_t$ to a target value related to $\rho_i$ by the flat value relation. Then there are
target values $w_1, \dots, w_n$ such that the flat environment
$(\mathrm{acc}(i_1), (\dots, (\mathrm{acc}(i_n), \mathsf{unit})\dots))$ evaluates in $\rho_t$ to
$(w_1, (\dots, (w_n, \mathsf{unit})\dots))$, and for each $k$ the index $i_k$ is less than the
length of $\rho$ and $w_k$ is related to $\rho_{i_k}$ by the flat value relation.
