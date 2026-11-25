# Restriction inversion for ranked typing

Let $n$ be a natural number, $\Delta$ an ownership context and $p$ a process. If $\Delta
\vdash^{\mathrm{rk}}_n \nu\,p$, then there is a capability $c$ with $\nu_c\Delta
\vdash^{\mathrm{rk}}_{n+1} p$, where $\nu_c\Delta$ is obtained from $\Delta$ by adding one to the
index of every variable name of its endpoints and then adding the entries $\mathrm{v}_0^{+} \mapsto
c$ and $\mathrm{v}_0^{-} \mapsto \bar c$ ($\bar c$: same rank, dual protocol).
