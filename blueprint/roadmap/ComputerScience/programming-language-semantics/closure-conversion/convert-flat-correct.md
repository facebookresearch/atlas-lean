# Correctness of flat closure conversion

Let $\rho$ be a source environment, $\rho_t$ a
target environment, $\mathrm{acc}$ a map from natural numbers to target terms, and $t$ a raw term
that evaluates to a source value $v$ in $\rho$. Suppose that for every free variable $i$ of $t$,
$i$ is less than the length of $\rho$ and $\mathrm{acc}(i)$ evaluates in $\rho_t$ to a target
value related by the flat value relation to the entry $\rho_i$ of $\rho$ at index $i$ (counting
from $0$). Then the flat conversion of $t$ with accessors $\mathrm{acc}$ evaluates in $\rho_t$ to
some target value related to $v$ by the flat value relation.
