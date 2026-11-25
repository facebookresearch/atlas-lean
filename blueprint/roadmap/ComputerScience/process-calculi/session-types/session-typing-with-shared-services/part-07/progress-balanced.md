# Global runtime progress at balanced interfaces given availability

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ a semantically balanced
ownership context (whenever $\Delta(e) = c$, there is $d$ with $\Delta(\bar e) = d$ and $d \approx
\bar c$) and $p$ a process with $\Gamma; \Delta \vdash_n p$ in which all services of $\Gamma$ are
available (every declared $\mathrm{c}_s$ is offered by a replicated unguarded input). Then $p$ is
idle for $\Gamma$ (a service template: built from $\mathbf{0}$ and inputs on declared triggers by
$\mid$, $\nu$ and replication) or $p \to q$ for some process $q$.
