# Closing an instantiated System F term binder

For every environment $\eta$ of model terms for $m$ term variables and System F terms $b \in \mathrm{Tm}_{n,m+1}$ and $a \in \mathrm{Tm}_{n,m}$, the [closing](close.md) of the [instantiation](../scoped-pure-system-f/instantiate-2.md) $b[a]$ under $\eta$ equals the closing of $b$ under the environment sending $0$ to the closing of $a$ under $\eta$ and $i + 1$ to $\eta(i)$.
