# Binder swapping preserves runtime typing

Let $n$, $k$ be natural numbers with $k + 1 < n$, $\Gamma$ a service environment, $\Delta$ an
ownership context and $p$ a process. If $\Gamma; \Delta \vdash_n p$, then $\Gamma; \Delta[k
\leftrightarrow k+1] \vdash_n p[k \leftrightarrow k+1]$, where $[k \leftrightarrow k+1]$ exchanges
the variable indices $k$ and $k+1$.
