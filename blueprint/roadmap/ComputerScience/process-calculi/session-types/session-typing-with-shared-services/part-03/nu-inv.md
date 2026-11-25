# Inversion of runtime typing for restriction

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context and $p$ a
process. If $\Gamma; \Delta \vdash_n \nu\,p$, then there is a capability $c$ with $\Gamma;
\nu_c\Delta \vdash_{n+1} p$, where $\nu_c\Delta$ is $\uparrow_0\Delta$ extended by $\mathrm{v}_0^{+}
\mapsto c$ and $\mathrm{v}_0^{-} \mapsto \bar c$.
