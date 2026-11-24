# Runtime typing is preserved by reverse scope extrusion

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context and $p$,
$q$ processes. If $\Gamma; \Delta \vdash_n \nu\,(p \mid \uparrow_0 q)$, then $\Gamma; \Delta
\vdash_n (\nu\,p) \mid q$.
