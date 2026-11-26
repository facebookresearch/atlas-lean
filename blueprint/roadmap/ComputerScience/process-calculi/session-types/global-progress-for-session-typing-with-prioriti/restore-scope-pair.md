# Restoring the bound pair preserves ranked typing

Let $n$ be a natural number, $\Delta$, $\Gamma$, $\Xi$ ownership contexts, $p$, $q$ processes and
$c$ a capability. Suppose $\Gamma \vdash^{\mathrm{rk}}_{n+1} p$, $\Xi \vdash^{\mathrm{rk}}_{n+1}
\uparrow_0 q$ and $\nu_c\Delta = \Gamma \cup \Xi$, where $\nu_c\Delta$ is $\Delta$ with every
variable name index raised by one and the entries $\mathrm{v}_0^{+} \mapsto c$, $\mathrm{v}_0^{-}
\mapsto \bar c$ added. Then $\Gamma[\mathrm{v}_0^{+} \mapsto c][\mathrm{v}_0^{-} \mapsto \bar c]
\vdash^{\mathrm{rk}}_{n+1} p$.
