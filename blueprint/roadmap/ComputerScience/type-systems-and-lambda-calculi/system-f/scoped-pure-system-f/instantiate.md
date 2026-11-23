# Instantiating the newest type binder of a type

For [types](ty.md) $B \in \mathrm{Ty}_{n+1}$ and $A \in \mathrm{Ty}_n$, the instantiation $B[A] \in \mathrm{Ty}_n$ is the [substitution](subst.md) of $B$ by the substitution sending $0$ to $A$ and $i + 1$ to $\alpha_i$: it replaces the newest type variable by $A$ and discharges its binder.
