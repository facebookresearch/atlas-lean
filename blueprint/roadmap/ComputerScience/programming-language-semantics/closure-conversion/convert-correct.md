# Correctness of closure conversion

Let $\rho$ be a list of source values, $\ell$ its
length, and $t$ a source term that evaluates to a source value $v$ in the environment $\rho$. Let
$\rho_t$ be a list of target values and $\mathit{acc}$ a family of target terms indexed by the
natural numbers that implement $\rho$ in $\rho_t$. Then there is a target value $w$ such that the
conversion of $t$ in a scope of $\ell$ variables with accessors $\mathit{acc}$ evaluates to $w$
in the environment $\rho_t$, and $v$ is related to $w$ by the value relation of closure
conversion.
