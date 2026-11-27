# Endpoint typing is invariant under scope extrusion

For every natural number $n$, ownership context $\Delta$ and processes $p$, $q$: $\Delta \vdash_n
(\nu\,p) \mid q$ if and only if $\Delta \vdash_n \nu\,(p \mid \uparrow_0 q)$ (endpoint typing),
where $\uparrow_0 q$ adds one to every free variable index of $q$.
