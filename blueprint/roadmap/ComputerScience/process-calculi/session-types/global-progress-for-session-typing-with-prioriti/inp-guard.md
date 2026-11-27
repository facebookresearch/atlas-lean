# Ranked input exposes its subject's guard condition

Let $n$ be a natural number, $\Delta$ an ownership context, $a$ a name and $p$ a process. If $\Delta
\vdash^{\mathrm{rk}}_n a(\cdot).p$, then there are an endpoint $e$ with name $a$ and a capability
$c$ of rank $k$ such that $\Delta(e) = c$ and $\mathrm{Min}_\Delta(e,k)$: every endpoint $d \ne e$
with an active capability in $\Delta$ has rank $> k$.
