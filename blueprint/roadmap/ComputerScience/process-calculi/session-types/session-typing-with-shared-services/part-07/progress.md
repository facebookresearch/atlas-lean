# Balanced runtime frontiers are idle or step given availability

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ a semantically balanced
ownership context (whenever $\Delta(e) = c$, there is $d$ with $\Delta(\bar e) = d$ and $d \approx
\bar c$) and $p$ a guarded frontier for $\Gamma$ with $\Gamma; \Delta \vdash_n p$ in which all
services of $\Gamma$ are available (every declared $\mathrm{c}_s$ is offered by a replicated
unguarded input). Then $p$ is idle for $\Gamma$ (a service template) or $p \to q$ for some process
$q$.
