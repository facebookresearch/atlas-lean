# Restriction inversion for conversion typing

Let $n$ be a natural number, $\Delta$ an ownership context and $p$ a process. If $\Delta
\vdash^{\simeq}_n \nu\,p$, then there is a capability $c$ with $\nu_c\Delta \vdash^{\simeq}_{n+1}
p$, where $\nu_c\Delta$ is $\uparrow_0\Delta$ (every variable name index of an endpoint raised by
one) extended by $\mathrm{v}_0^{+} \mapsto c$ and $\mathrm{v}_0^{-} \mapsto \bar c$.
