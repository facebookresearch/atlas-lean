# Adding a role unused by the partner preserves conversion typing

Let $n$ be a natural number, $\Gamma$, $\Xi$ ownership contexts, $p$, $q$ processes, $e$ an endpoint
whose name is scoped at depth $n$ and does not occur in $q$, and $c$ a capability with $(\Gamma \cup
\Xi)(e) = c$. If $\Gamma \vdash^{\simeq}_n p$ and $\Xi \vdash^{\simeq}_n q$, then $\Gamma[e \mapsto
c] \vdash^{\simeq}_n p$.
