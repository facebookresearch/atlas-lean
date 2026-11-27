# Runtime typing absorbs a role absent from its parallel partner

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$, $\Xi$ ownership contexts,
$p$, $q$ processes, $e$ an endpoint whose name is scoped at depth $n$ and does not occur in $q$, and
$c$ a capability with $(\Delta \cup \Xi)(e) = c$. If $\Gamma; \Delta \vdash_n p$ and $\Gamma; \Xi
\vdash_n q$, then $\Gamma; \Delta[e \mapsto c] \vdash_n p$.
