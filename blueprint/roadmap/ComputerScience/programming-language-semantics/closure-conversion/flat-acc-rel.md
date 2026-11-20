# Accessors implementing the free variables of a term

Let $\rho$ be a list of source
values of length $|\rho|$, $\rho_t$ a list of target values, $\mathrm{acc}$ a map assigning a target
term to each natural number, and $t$ a raw term. The accessors $\mathrm{acc}$ implement $t$ for
$\rho$ in $\rho_t$ when, for every free variable $i$ of $t$, $i < |\rho|$ and $\mathrm{acc}(i)$
evaluates in the target environment $\rho_t$ to a target value that is related, by the flat value
relation, to the entry of $\rho$ at index $i$ (counting from $0$).
