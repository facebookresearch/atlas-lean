# Endpoint substitution preserves ranked typing

Let $n$ be a natural number, $\Delta$ an ownership context, $b$ a name scoped at depth $n$, $r$ a
polarity, $c$ a capability and $p$ a process, with the endpoint $b^{r}$ not in the domain of
$\Delta$. If $(\uparrow_0\Delta)[\mathrm{v}_0^{r} \mapsto c] \vdash^{\mathrm{rk}}_{n+1} p$, where
$\uparrow_0\Delta$ raises the index of every variable name of an endpoint by one, then $\Delta[b^{r}
\mapsto c] \vdash^{\mathrm{rk}}_n p\{b\}$, where $p\{b\}$ replaces $\mathrm{v}_0$ by $b$ and lowers
larger indices by one.
