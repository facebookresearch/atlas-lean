# Endpoint typing absorbs a role absent from its parallel partner

Let $n$ be a natural number, $\Gamma$, $\Xi$ ownership contexts, $p$, $q$ processes, $e$ an endpoint
whose name is scoped at depth $n$ and does not occur in $q$, and $c$ a capability with $(\Gamma \cup
\Xi)(e) = c$. If $\Gamma \vdash_n p$ and $\Xi \vdash_n q$, then $\Gamma[e \mapsto c] \vdash_n p$.
