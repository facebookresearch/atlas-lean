# Output on a declared shared name is a service invocation

Let $n$, $s$ be natural numbers, $\Gamma$ a service environment with $\Gamma(s) = \sigma = (\pi, r,
c)$, $\Delta$ an ownership context, $b$ a name and $p$ a process with $\Gamma; \Delta \vdash_n
\overline{\mathrm{c}_s}\langle b\rangle.p$. Then there are an endpoint $e$ with name $b$ and
polarity $r$ and a capability $v$ with $\Delta(e) = v$, $v \approx c$, $\pi$ below the rank of every
active capability of $\Delta$, and $\Gamma; \Delta \setminus e \vdash_n p$.
