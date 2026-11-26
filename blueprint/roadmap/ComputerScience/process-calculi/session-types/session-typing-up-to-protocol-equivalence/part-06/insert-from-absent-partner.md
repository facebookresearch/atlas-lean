# Adding a role unused by the partner preserves conversion ranked typing

Let $n$ be a natural number, $\Gamma$, $\Xi$ ownership contexts, $p$, $q$ processes, $e$ an endpoint
whose name is scoped at depth $n$ and does not occur in $q$, and $c$ a capability with $(\Gamma \cup
\Xi)(e) = c$. If $\Gamma \vdash^{\mathrm{rk}\simeq}_n p$ and $\Xi \vdash^{\mathrm{rk}\simeq}_n q$,
then $\Gamma[e \mapsto c] \vdash^{\mathrm{rk}\simeq}_n p$.
