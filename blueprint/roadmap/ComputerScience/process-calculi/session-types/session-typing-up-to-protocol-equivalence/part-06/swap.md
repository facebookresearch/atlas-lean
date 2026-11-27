# Binder swap preserves conversion ranked typing

Let $n$, $k$ be natural numbers with $k + 1 < n$, $\Delta$ an ownership context and $p$ a process.
If $\Delta \vdash^{\mathrm{rk}\simeq}_n p$, then $\Delta[k \leftrightarrow k+1]
\vdash^{\mathrm{rk}\simeq}_n p[k \leftrightarrow k+1]$, where $[k \leftrightarrow k+1]$ exchanges
the variable indices $k$ and $k+1$ (raised by one under each binder of $p$; applied to the names of
the endpoints of $\Delta$).
