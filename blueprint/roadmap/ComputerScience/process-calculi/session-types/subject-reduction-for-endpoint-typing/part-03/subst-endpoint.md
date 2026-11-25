# Endpoint typing under substitution of a transmitted endpoint

Let $n$ be a natural number, $\Delta$ an ownership context, $b$ a name scoped at depth $n$, $r$ a
polarity, $c$ a capability and $p$ a process, with $b^{r}$ not in the domain of $\Delta$. If
$(\uparrow_0\Delta)[\mathrm{v}_0^{r} \mapsto c] \vdash_{n+1} p$ (endpoint typing), then
$\Delta[b^{r} \mapsto c] \vdash_n p\{b\}$, where $p\{b\}$ replaces $\mathrm{v}_0$ by $b$ and lowers
larger indices by one.
