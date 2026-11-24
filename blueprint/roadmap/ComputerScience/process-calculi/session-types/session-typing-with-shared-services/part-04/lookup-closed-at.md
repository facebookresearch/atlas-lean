# Each owned key of a runtime typing is scoped at ambient depth

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context and $p$ a
process with $\Gamma; \Delta \vdash_n p$. If $\Delta(z) = t$ for an endpoint $z$ and a capability
$t$, then the name of $z$ is scoped at depth $n$ (a constant, or a variable with index $< n$).
