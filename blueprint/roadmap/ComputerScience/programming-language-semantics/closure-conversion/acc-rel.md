# Accessors implementing a source environment

Let $\rho$ be a list of source values,
$\rho_t$ a list of target values and $\mathit{acc}$ a family of target terms indexed by the
natural numbers. The accessors $\mathit{acc}$ implement $\rho$ in $\rho_t$ when, for every index
$i$ less than the length of $\rho$, there is a target value $w$ such that $\mathit{acc}(i)$
evaluates to $w$ in the environment $\rho_t$ and the entry of $\rho$ at index $i$ is related to
$w$ by the value relation of closure conversion.
