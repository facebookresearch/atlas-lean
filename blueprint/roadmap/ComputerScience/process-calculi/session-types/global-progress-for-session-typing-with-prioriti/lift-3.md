# Binder lifting preserves ranked typing

Let $n$, $k$ be natural numbers, $\Delta$ an ownership context and $p$ a process. If $\Delta
\vdash^{\mathrm{rk}}_n p$, then $\uparrow_k\Delta \vdash^{\mathrm{rk}}_{n+1} \uparrow_k p$, where
$\uparrow_k$ adds one to every variable index $\ge k$ (in $p$, the cutoff is raised by one under
each binder; in $\Delta$, it is applied to the name of every endpoint).
