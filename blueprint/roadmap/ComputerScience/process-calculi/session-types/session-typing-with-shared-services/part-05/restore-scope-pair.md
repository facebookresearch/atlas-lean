# Runtime typing restores both bound roles to the restricted side

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$, $\Lambda$, $\Xi$ ownership
contexts, $p$, $q$ processes and $c$ a capability with $\Gamma; \Lambda \vdash_{n+1} p$, $\Gamma;
\Xi \vdash_{n+1} \uparrow_0 q$ and $\nu_c\Delta = \Lambda \cup \Xi$. Then $\Gamma;
\Lambda[\mathrm{v}_0^{+} \mapsto c][\mathrm{v}_0^{-} \mapsto \bar c] \vdash_{n+1} p$.
