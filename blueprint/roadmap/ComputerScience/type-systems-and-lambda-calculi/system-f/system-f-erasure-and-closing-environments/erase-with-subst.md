# Erasure of a term substitution

For every term substitution $\sigma$ from $m$ to $k$ term variables, environment $\eta$ of untyped terms for $k$ variables and System F term $t$, the [erasure](erase-with.md) under $\eta$ of the [substitution](../scoped-pure-system-f/subst-2.md) $t[\sigma]$ equals the erasure of $t$ under the environment $i \mapsto |\sigma(i)|_\eta$.
