# Endpoint substitution preserves conversion ranked typing

Let $n$ be a natural number, $\Delta$ an ownership context, $b$ a name scoped at depth $n$, $r$ a
polarity, $c$, $v$ capabilities with $v \approx c$ and $p$ a process, with $b^{r}$ not in the domain
of $\Delta$. If $(\uparrow_0\Delta)[\mathrm{v}_0^{r} \mapsto c] \vdash^{\mathrm{rk}\simeq}_{n+1} p$,
then $\Delta[b^{r} \mapsto v] \vdash^{\mathrm{rk}\simeq}_n p\{b\}$, where $p\{b\}$ replaces
$\mathrm{v}_0$ by $b$ and lowers larger indices by one.
