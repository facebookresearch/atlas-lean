# Forward scope extrusion preserves ranked typing

Let $n$ be a natural number, $\Delta$ an ownership context and $p$, $q$ processes. If $\Delta
\vdash^{\mathrm{rk}}_n (\nu\,p) \mid q$, then $\Delta \vdash^{\mathrm{rk}}_n \nu\,(p \mid \uparrow_0
q)$, where $\uparrow_0 q$ adds one to every free variable index of $q$.
