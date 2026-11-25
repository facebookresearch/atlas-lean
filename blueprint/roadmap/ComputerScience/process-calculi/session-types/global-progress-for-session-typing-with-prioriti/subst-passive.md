# Passive substitution preserves ranked typing

Let $n$ be a natural number, $\Delta$ an ownership context, $p$ a process and $b$ a name scoped at
depth $n$. If $\uparrow_0\Delta \vdash^{\mathrm{rk}}_{n+1} p$, where $\uparrow_0\Delta$ adds one to
the index of every variable name of an endpoint of $\Delta$, then $\Delta \vdash^{\mathrm{rk}}_n
p\{b\}$, where $p\{b\}$ replaces the variable $\mathrm{v}_0$ of $p$ by $b$ and lowers larger indices
by one.
