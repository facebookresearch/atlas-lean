# Runtime typing under passive name substitution

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context, $p$ a
process and $b$ a name scoped at depth $n$. If $\Gamma; \uparrow_0\Delta \vdash_{n+1} p$, then
$\Gamma; \Delta \vdash_n p\{b\}$.
