# Closing an instantiated Fω term binder

For every environment $\eta$ of model terms for $m$ term variables, $b \in \mathrm{Tm}_{\Delta,m+1}$
and $a \in \mathrm{Tm}_{\Delta,m}$, the [closing](close.md) of the
[instantiation](../scoped-pure-f-terms/instantiate.md) $b[a]$ under $\eta$ equals the closing of $b$
under the environment sending $0$ to $a\{\eta\}$ and $i + 1$ to $\eta(i)$.
