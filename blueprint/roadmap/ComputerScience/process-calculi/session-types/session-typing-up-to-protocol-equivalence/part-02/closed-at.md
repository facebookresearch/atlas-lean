# Conversion-typed processes are well scoped

Let $n$ be a natural number, $\Delta$ an ownership context and $p$ a process. If $\Delta
\vdash^{\simeq}_n p$, then $p$ is scoped at depth $n$: every variable occurring in $p$ under $m$
binders of $p$ has index $< n + m$.
