# Inversion of runtime typing for the nil process

Let $n$ be a natural number, $\Gamma$ a service environment and $\Delta$ an ownership context. If
$\Gamma; \Delta \vdash_n \mathbf{0}$, then every capability of $\Delta$ has head $\mathrm{end}$,
every endpoint of $\Delta$ has a name scoped at depth $n$, and $\Delta$ is separated from $\Gamma$.
