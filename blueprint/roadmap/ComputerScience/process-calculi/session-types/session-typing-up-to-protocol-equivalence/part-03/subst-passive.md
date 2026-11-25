# Passive name substitution preserves conversion typing

Let $n$ be a natural number, $\Delta$ an ownership context, $p$ a process and $b$ a name scoped at
depth $n$. If $\uparrow_0\Delta \vdash^{\simeq}_{n+1} p$, where $\uparrow_0\Delta$ raises every
variable name index of an endpoint by one, then $\Delta \vdash^{\simeq}_n p\{b\}$.
