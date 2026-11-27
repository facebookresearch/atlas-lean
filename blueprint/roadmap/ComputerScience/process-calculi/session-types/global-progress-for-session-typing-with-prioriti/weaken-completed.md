# Weakening ranked typing by a completed capability

Let $n$ be a natural number, $\Delta$ an ownership context, $p$ a process, $z$ an endpoint not in
the domain of $\Delta$ whose name is scoped at depth $n$, and $u$ a capability whose protocol has
head $\mathrm{end}$. If $\Delta \vdash^{\mathrm{rk}}_n p$, then $\Delta[z \mapsto u]
\vdash^{\mathrm{rk}}_n p$.
