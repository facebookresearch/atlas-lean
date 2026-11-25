# Runtime-typed processes are scoped at the ambient depth

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context and $p$ a
process. If $\Gamma; \Delta \vdash_n p$, then $p$ is scoped at depth $n$: every variable occurring
in $p$ under $m$ binders of $p$ has index $< n + m$.
