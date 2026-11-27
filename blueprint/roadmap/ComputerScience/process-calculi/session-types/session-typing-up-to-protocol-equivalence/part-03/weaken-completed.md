# Weakening conversion typing by a completed capability

Let $n$ be a natural number, $\Delta$ an ownership context, $p$ a process, $z$ an endpoint not in
the domain of $\Delta$ with name scoped at depth $n$ and $u$ a capability whose protocol has head
$\mathrm{end}$. If $\Delta \vdash^{\simeq}_n p$, then $\Delta[z \mapsto u] \vdash^{\simeq}_n p$.
