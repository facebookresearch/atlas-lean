# Runtime typing separates owned names from shared services

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context and $p$ a
process. If $\Gamma; \Delta \vdash_n p$, then $\Delta$ is separated from $\Gamma$: no endpoint owned
by $\Delta$ is named by the trigger $\mathrm{c}_s$ of a service $s$ declared in $\Gamma$.
