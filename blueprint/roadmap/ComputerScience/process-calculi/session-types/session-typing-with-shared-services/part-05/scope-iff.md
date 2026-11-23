# Runtime typing is invariant under scope extrusion

For every natural number $n$, service environment $\Gamma$, ownership context $\Delta$ and processes
$p$, $q$: $\Gamma; \Delta \vdash_n (\nu\,p) \mid q$ if and only if $\Gamma; \Delta \vdash_n \nu\,(p
\mid \uparrow_0 q)$, where $\uparrow_0 q$ adds one to every free variable index of $q$.
