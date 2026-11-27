# Instantiating the newest term binder of a term

For [terms](tm.md) $b \in \mathrm{Tm}_{n,m+1}$ and $a \in \mathrm{Tm}_{n,m}$, the instantiation $b[a] \in \mathrm{Tm}_{n,m}$ is the [substitution](subst-2.md) of $b$ by the substitution sending $0$ to $a$ and $i + 1$ to $x_i$: it replaces the newest term variable by $a$ and discharges its binder.
