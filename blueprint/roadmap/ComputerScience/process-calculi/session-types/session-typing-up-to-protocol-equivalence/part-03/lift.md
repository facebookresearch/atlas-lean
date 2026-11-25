# Lifting past a binder preserves conversion typing

Let $n$, $k$ be natural numbers, $\Delta$ an ownership context and $p$ a process. If $\Delta
\vdash^{\simeq}_n p$, then $\uparrow_k\Delta \vdash^{\simeq}_{n+1} \uparrow_k p$, where $\uparrow_k$
adds one to every variable index $\ge k$ (in $p$ the cutoff is raised under binders; in $\Delta$ it
is applied to the names of the endpoints).
