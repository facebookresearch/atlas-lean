# Lifting a term substitution under a term binder

For a term substitution $\sigma$ assigning to each $i < m$ a [term](tm.md) $\sigma(i) \in
\mathrm{Tm}_{\Delta,k}$, the lifted substitution $\sigma^{\uparrow}$ sends $0$ to $x_0$ and $i + 1$
to $\sigma(i)$ [renamed](rename.md) by $j \mapsto j + 1$; it substitutes for $m + 1$ variables with
terms over $k + 1$ variables.
