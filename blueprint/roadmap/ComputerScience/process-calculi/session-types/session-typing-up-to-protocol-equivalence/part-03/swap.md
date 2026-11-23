# Swapping adjacent binders preserves conversion typing

Let $n$, $k$ be natural numbers with $k + 1 < n$, $\Delta$ an ownership context and $p$ a process.
If $\Delta \vdash^{\simeq}_n p$, then $\Delta[k \leftrightarrow k+1] \vdash^{\simeq}_n p[k
\leftrightarrow k+1]$, where $[k \leftrightarrow k+1]$ exchanges the variable indices $k$ and $k+1$
(in $p$ the indices are raised by one under each binder; in $\Delta$ it is applied to the names of
the endpoints).
