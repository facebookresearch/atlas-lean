# Inversion of runtime typing for input on a shared name

Let $n$, $s$ be natural numbers, $\Gamma$ a service environment with $\Gamma(s) = (\pi, r, c)$,
$\Delta$ an ownership context and $p$ a process with $\Gamma; \Delta \vdash_n
\mathrm{c}_s(\cdot).p$. Then every capability of $\Delta$ has head $\mathrm{end}$, every endpoint of
$\Delta$ has a name scoped at depth $n$, $\Delta$ is separated from $\Gamma$, and $\Gamma;
\{\mathrm{v}_0^{r} \mapsto c\} \vdash_{n+1} p$.
